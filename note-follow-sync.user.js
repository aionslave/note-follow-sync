// ==UserScript==
// @name         黒峰 note 相互フォロー整理
// @namespace    kuromine.local
// @version      0.1.4
// @description  noteのフォロー中・フォロワーを比較し、片思い解除とフォロバ漏れを確認後に小分け処理します。
// @author       KuroMine
// @match        https://note.com/*
// @run-at       document-idle
// @grant        none
// ==/UserScript==

/*
  黒峰 note 相互フォロー整理 v0.1.4

  対応:
  - PC: Chrome + Tampermonkey系ユーザースクリプト拡張
  - iPhone/iPad: Safari + ユーザースクリプト対応拡張

  使い方:
  1. noteへログインし、自分のクリエイターページを開く。
  2. 右下の「黒」ボタンからパネルを開く。
  3. note IDを確認して「差分を調査」を押す。
  4. 解除候補またはフォロバ漏れを確認し、対象を選択して実行する。

  安全設計:
  - 調査しただけではフォロー状態を変更しません。
  - 自分のプロフィールからnote IDを確認し、自分のアカウントだけ操作できます。
  - 他人のアカウントは調査専用です。
  - noteの公開一覧が1,000人で打ち切られる場合は参考値として表示します。
  - 実行前に対象一覧と確認ダイアログを表示します。
  - 1回最大20件、操作間隔は4〜7秒です。
  - 一覧取得が不完全な場合は実行を禁止します。
  - データはこの端末のブラウザ内だけに保存します。
*/

(() => {
  'use strict';

  if (window.top !== window.self) return;
  if (document.getElementById('km-note-sync-host')) return;

  const APP = {
    name: '黒峰 note 相互フォロー整理',
    version: '0.1.4',
    pageSize: 20,
    maxPublicPages: 50,
    scanDelayMin: 550,
    scanDelayMax: 850,
    actionDelayMin: 4000,
    actionDelayMax: 7000,
    maxBatch: 20,
    queueMaxAgeMs: 2 * 60 * 60 * 1000,
  };

  const KEY = {
    settings: 'km_note_sync_settings_v1',
    scan: 'km_note_sync_scan_v1',
    protectedIds: 'km_note_sync_protected_v1',
    queue: 'km_note_sync_queue_v1',
    lastLog: 'km_note_sync_last_log_v1',
  };

  const state = {
    account: '',
    ownerAccount: '',
    scan: null,
    protectedIds: new Set(),
    selected: new Set(),
    activeTab: 'followingOnly',
    busy: false,
    processing: false,
    stopRequested: false,
    minimized: true,
    status: '',
    statusType: 'normal',
    progress: null,
    root: null,
    shadow: null,
  };

  const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
  const randomBetween = (min, max) => Math.round(min + Math.random() * (max - min));
  const nowIso = () => new Date().toISOString();
  const escapeHtml = (value) => String(value ?? '')
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
    .replaceAll("'", '&#039;');

  function readJson(key, fallback) {
    try {
      const raw = localStorage.getItem(key);
      return raw ? JSON.parse(raw) : fallback;
    } catch (_) {
      return fallback;
    }
  }

  function writeJson(key, value) {
    localStorage.setItem(key, JSON.stringify(value));
  }

  function removeStored(key) {
    localStorage.removeItem(key);
  }

  function normalizeAccount(value) {
    return String(value || '')
      .trim()
      .replace(/^@/, '')
      .replace(/^https?:\/\/note\.com\//i, '')
      .split(/[/?#]/)[0];
  }

  function validAccount(value) {
    return /^[A-Za-z0-9_-]{1,64}$/.test(value);
  }

  function profileAccountFromPath(pathname = location.pathname) {
    const firstPart = String(pathname || '').split('/').filter(Boolean)[0] || '';
    const account = normalizeAccount(firstPart);
    return validAccount(account) ? account : '';
  }

  function ownerAccountFromDocument(doc = document, pathname = location.pathname) {
    if (!doc?.querySelector) return '';
    const account = profileAccountFromPath(pathname);
    const main = doc.querySelector('main');
    if (!account || !main) return '';

    // 自分のクリエイターページにだけ表示されるプロフィール設定操作で本人を確認する。
    const hasOwnProfileControl = Array.from(main.querySelectorAll('a[href], button'))
      .some((element) => {
        const text = (element.textContent || '').trim().replace(/\s+/g, '');
        const label = (element.getAttribute('aria-label') || '').trim().replace(/\s+/g, '');
        const href = element.getAttribute('href') || '';
        if (/\/settings\/profile(?:[/?#]|$)/.test(href)) return true;
        if (element.tagName !== 'BUTTON') return false;
        return text === '設定' || text === 'プロフィールを編集'
          || label === '設定' || label === 'プロフィールを編集';
      });

    return hasOwnProfileControl ? account : '';
  }

  function currentPageNumber() {
    const page = Number(new URL(location.href).searchParams.get('page') || 1);
    return Number.isFinite(page) && page > 0 ? Math.floor(page) : 1;
  }

  function listUrl(account, kind, page = 1) {
    const url = new URL(`/${account}/${kind}`, location.origin);
    if (page > 1) url.searchParams.set('page', String(page));
    return url.toString();
  }

  function profileIdFromHref(href) {
    try {
      const url = new URL(href, location.origin);
      if (url.hostname !== 'note.com') return '';
      const parts = url.pathname.split('/').filter(Boolean);
      if (parts.length !== 1) return '';
      return normalizeAccount(parts[0]);
    } catch (_) {
      return '';
    }
  }

  function visible(element) {
    if (!element) return false;
    const style = getComputedStyle(element);
    const rect = element.getBoundingClientRect();
    return style.display !== 'none' && style.visibility !== 'hidden' && rect.width > 0 && rect.height > 0;
  }

  function headingForKind(doc, kind) {
    const expected = kind === 'followings' ? 'フォロー' : 'フォロワー';
    return Array.from(doc.querySelectorAll('main h1, main h2, main h3'))
      .find((node) => (node.textContent || '').trim() === expected) || null;
  }

  function profileAnchorInRow(row) {
    // noteの独自ドメイン利用者は、プロフィールリンクがnote.comではなくなる。
    // 一覧カード直下のタイトル付きリンクを優先し、通常URLは従来どおり判定する。
    const directProfileAnchor = Array.from(row.children || [])
      .find((element) => element.tagName === 'A'
        && element.hasAttribute('href')
        && (element.getAttribute('title') || '').trim());
    if (directProfileAnchor) return directProfileAnchor;

    return Array.from(row.querySelectorAll('a[href]'))
      .find((anchor) => profileIdFromHref(anchor.getAttribute('href'))) || null;
  }

  function profileIdFromRow(row) {
    const anchor = profileAnchorInRow(row);
    if (!anchor) return '';

    const idFromUrl = profileIdFromHref(anchor.getAttribute('href'));
    if (idFromUrl) return idFromUrl;

    // 独自ドメインのカードでも、表示上のnote ID（例: chocobra）は残っている。
    const likelyNodes = [
      row.querySelector('.font-bold')?.nextElementSibling,
      ...row.querySelectorAll('.break-all, [class*="text-text-secondary"]'),
    ].filter(Boolean);

    for (const node of likelyNodes) {
      const id = normalizeAccount((node.textContent || '').trim());
      if (validAccount(id)) return id;
    }

    // CSSクラス変更時の予備。プロフィール名と同じ文字列はID候補から外す。
    const profileName = (anchor.getAttribute('title') || '').trim();
    const leafNodes = Array.from(row.querySelectorAll('*'))
      .filter((node) => node.children.length === 0);
    for (const node of leafNodes) {
      const text = (node.textContent || '').trim();
      if (text !== profileName && validAccount(text)) return normalizeAccount(text);
    }
    return '';
  }

  function profileListInSection(section) {
    if (!section) return null;
    const candidates = Array.from(section.querySelectorAll('ul'));
    return candidates
      .map((list) => ({
        list,
        score: Array.from(list.children).filter((child) => profileAnchorInRow(child)).length,
      }))
      .sort((a, b) => b.score - a.score)
      .find((item) => item.score > 0)?.list || null;
  }

  function extractTotal(heading) {
    if (!heading) return 0;
    const header = heading.parentElement;
    const text = header ? (header.textContent || '') : '';
    const match = text.match(/([\d,]+)\s*人/);
    return match ? Number(match[1].replaceAll(',', '')) : 0;
  }

  function publicPageCount(total, detectedPages = 1) {
    const numericTotal = Number(total);
    const numericDetected = Number(detectedPages);
    const pagesFromTotal = Number.isFinite(numericTotal) && numericTotal > 0
      ? Math.ceil(numericTotal / APP.pageSize)
      : 0;
    const fallbackPages = Number.isFinite(numericDetected) && numericDetected > 0
      ? Math.floor(numericDetected)
      : 1;

    // noteの公開一覧は20人×50ページ＝最大1,000人まで。
    // プロフィール上の合計人数が1,000人を超えても、51ページ目以降は取得しない。
    return Math.min(Math.max(1, pagesFromTotal || fallbackPages), APP.maxPublicPages);
  }

  function extractMaxPage(section, total) {
    let max = 1;
    let foundPageLink = false;
    if (section) {
      for (const anchor of section.querySelectorAll('a[href*="page="]')) {
        try {
          const value = Number(new URL(anchor.getAttribute('href'), location.origin).searchParams.get('page'));
          if (Number.isFinite(value) && value > 0) {
            foundPageLink = true;
            max = Math.max(max, value);
          }
        } catch (_) {
          // Ignore malformed links.
        }
      }
    }
    return publicPageCount(total, foundPageLink ? max : 1);
  }

  function recordFromRow(row, page) {
    const anchor = profileAnchorInRow(row);
    if (!anchor) return null;
    const id = profileIdFromRow(row);
    if (!id) return null;
    const name = (anchor.getAttribute('title') || '').trim()
      || (row.querySelector('.font-bold')?.textContent || '').trim()
      || `@${id}`;
    const button = row.querySelector('button[aria-pressed], button[data-name="ToggleButton"]');
    return {
      id,
      name,
      url: new URL(anchor.getAttribute('href'), location.origin).toString(),
      page,
      creatorKey: row.getAttribute('data-creator-key') || '',
      pressed: button?.getAttribute('aria-pressed') === 'true',
    };
  }

  function parseListDocument(doc, kind, page) {
    const heading = headingForKind(doc, kind);
    const label = kind === 'followings' ? 'フォロー' : 'フォロワー';
    if (!heading) {
      const suffix = page > 1 ? `${page}ページ目に` : '';
      throw new Error(`${label}一覧の${suffix}データがありません（非公開・削除・公開上限の可能性）`);
    }
    const section = heading.closest('section') || heading.parentElement?.parentElement || null;
    const total = extractTotal(heading);
    const list = profileListInSection(section);
    if (!list && total === 0) return { records: [], total: 0, maxPage: 1 };
    if (!list) throw new Error(`${label}一覧のデータを確認できませんでした`);

    const records = Array.from(list.children)
      .map((row) => recordFromRow(row, page))
      .filter(Boolean);
    const maxPage = extractMaxPage(section, total);
    return { records, total, maxPage };
  }

  function uniqueRecords(records) {
    const map = new Map();
    for (const record of records) {
      if (!map.has(record.id)) map.set(record.id, record);
    }
    return Array.from(map.values());
  }

  function compareLists(followings, followers) {
    const followingMap = new Map(followings.map((record) => [record.id, record]));
    const followerMap = new Map(followers.map((record) => [record.id, record]));
    const followingOnly = followings.filter((record) => !followerMap.has(record.id));
    const followerOnly = followers.filter((record) => !followingMap.has(record.id));
    const mutual = followings.filter((record) => followerMap.has(record.id));
    return { followingOnly, followerOnly, mutual };
  }

  async function fetchDocument(account, kind, page) {
    if (!Number.isInteger(page) || page < 1 || page > APP.maxPublicPages) {
      throw new RangeError(`取得ページは1〜${APP.maxPublicPages}ページまでです`);
    }
    const response = await fetch(listUrl(account, kind, page), {
      method: 'GET',
      credentials: 'include',
      cache: 'no-store',
    });
    if (!response.ok) throw new Error(`一覧取得エラー: HTTP ${response.status}`);
    const html = await response.text();
    return new DOMParser().parseFromString(html, 'text/html');
  }

  async function scanKind(account, kind, onProgress) {
    const firstDoc = await fetchDocument(account, kind, 1);
    const first = parseListDocument(firstDoc, kind, 1);
    const all = [...first.records];
    // ページ検出側に不具合があっても、取得処理では必ず50ページ以内に止める。
    const pages = publicPageCount(first.total, first.maxPage);
    onProgress?.(1, pages);

    for (let page = 2; page <= pages && page <= APP.maxPublicPages; page += 1) {
      await sleep(randomBetween(APP.scanDelayMin, APP.scanDelayMax));
      const doc = await fetchDocument(account, kind, page);
      const parsed = parseListDocument(doc, kind, page);
      if (!parsed.records.length) break;
      all.push(...parsed.records);
      onProgress?.(page, pages);
    }

    const records = uniqueRecords(all);
    const total = first.total || records.length;
    const publiclyCapped = total > pages * APP.pageSize;
    const accessibleExpected = publiclyCapped ? pages * APP.pageSize : total;
    const accessibleComplete = records.length === accessibleExpected;
    return {
      records,
      total,
      expected: total,
      accessibleExpected,
      accessibleComplete,
      publiclyCapped,
      partial: publiclyCapped,
      complete: accessibleComplete && !publiclyCapped,
      pages,
    };
  }

  function setStatus(message, type = 'normal') {
    state.status = message;
    state.statusType = type;
    render();
  }

  function saveSettings() {
    writeJson(KEY.settings, {
      account: state.account,
      ownerAccount: state.ownerAccount,
    });
  }

  function saveProtected() {
    writeJson(KEY.protectedIds, Array.from(state.protectedIds));
  }

  function loadState() {
    const settings = readJson(KEY.settings, {});
    const savedOwner = normalizeAccount(settings.ownerAccount || '');
    const detectedOwner = ownerAccountFromDocument();
    const ownerChanged = Boolean(detectedOwner && detectedOwner !== savedOwner);
    state.ownerAccount = detectedOwner || savedOwner;
    state.account = ownerChanged
      ? detectedOwner
      : normalizeAccount(settings.account || state.ownerAccount);
    state.protectedIds = new Set(readJson(KEY.protectedIds, []));
    const scan = readJson(KEY.scan, null);
    if (scan?.account === state.account) state.scan = scan;
    if (detectedOwner && (ownerChanged || !settings.account)) saveSettings();
  }

  function refreshOwnerAccount() {
    const detectedOwner = ownerAccountFromDocument();
    if (!detectedOwner) return '';
    if (detectedOwner !== state.ownerAccount) {
      state.ownerAccount = detectedOwner;
      if (!state.account) state.account = detectedOwner;
      saveSettings();
    }
    return detectedOwner;
  }

  function scanIsComplete(scan = state.scan) {
    return Boolean(scan?.complete && scan.followings?.complete && scan.followers?.complete);
  }

  function scanIsPartial(scan = state.scan) {
    return Boolean(scan?.partial || scan?.followings?.publiclyCapped || scan?.followers?.publiclyCapped);
  }

  function isOwnerAccount(account = state.account) {
    const normalizedOwner = normalizeAccount(state.ownerAccount);
    return Boolean(normalizedOwner && normalizeAccount(account) === normalizedOwner);
  }

  function actionsAllowed(scan = state.scan) {
    return Boolean(
      scanIsComplete(scan)
      && isOwnerAccount(scan?.account)
      && normalizeAccount(state.account) === normalizeAccount(scan?.account),
    );
  }

  async function startScan() {
    if (state.busy || state.processing) return;
    const detectedOwner = refreshOwnerAccount();
    const input = state.shadow.querySelector('#km-account');
    if (detectedOwner && input && !normalizeAccount(input.value)) input.value = detectedOwner;
    const account = normalizeAccount(input?.value || state.account);
    if (!validAccount(account)) {
      setStatus('note IDを確認してください', 'error');
      return;
    }

    state.account = account;
    saveSettings();
    state.busy = true;
    state.scan = null;
    state.selected.clear();
    state.progress = { kind: 'followings', page: 0, pages: 0 };
    setStatus('フォロー中を調査しています…');

    try {
      const followings = await scanKind(account, 'followings', (page, pages) => {
        state.progress = { kind: 'followings', page, pages };
        render();
      });

      state.progress = { kind: 'followers', page: 0, pages: 0 };
      setStatus('フォロワーを調査しています…');
      const followers = await scanKind(account, 'followers', (page, pages) => {
        state.progress = { kind: 'followers', page, pages };
        render();
      });

      const diff = compareLists(followings.records, followers.records);
      const partial = followings.publiclyCapped || followers.publiclyCapped;
      const accessibleComplete = followings.accessibleComplete && followers.accessibleComplete;
      const complete = followings.complete && followers.complete;
      state.scan = {
        version: APP.version,
        account,
        scannedAt: nowIso(),
        complete,
        partial,
        accessibleComplete,
        followings,
        followers,
        followingOnly: diff.followingOnly,
        followerOnly: diff.followerOnly,
        mutual: diff.mutual,
      };
      writeJson(KEY.scan, state.scan);
      state.progress = null;
      if (complete) {
        const mode = isOwnerAccount(account) ? '' : '（他人のアカウントは調査専用）';
        setStatus(`調査完了：解除候補 ${diff.followingOnly.length}人／フォロバ漏れ ${diff.followerOnly.length}人${mode}`, 'success');
      } else if (partial && accessibleComplete) {
        setStatus('公開上限まで調査完了：先頭1,000人までの参考比較です。全体の差分ではありません', 'warning');
      } else {
        setStatus('取得件数が合いません。時間を置いて再調査してください', 'error');
      }
    } catch (error) {
      state.progress = null;
      setStatus(`調査失敗：${error.message}`, 'error');
    } finally {
      state.busy = false;
      render();
    }
  }

  function queueForAction(action, records) {
    const kind = action === 'unfollow' ? 'followings' : 'followers';
    const sorted = [...records].sort((a, b) => {
      if (action === 'unfollow') return b.page - a.page || a.id.localeCompare(b.id);
      return a.page - b.page || a.id.localeCompare(b.id);
    });
    return {
      version: APP.version,
      id: `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
      account: state.scan?.account || state.account,
      action,
      kind,
      createdAt: Date.now(),
      paused: false,
      index: 0,
      items: sorted,
      results: [],
    };
  }

  function getQueue() {
    const queue = readJson(KEY.queue, null);
    if (!queue) return null;
    if (!queue.createdAt || Date.now() - queue.createdAt > APP.queueMaxAgeMs) {
      removeStored(KEY.queue);
      return null;
    }
    return queue;
  }

  function saveQueue(queue) {
    writeJson(KEY.queue, queue);
  }

  function stopQueue(message = '処理を停止しました') {
    state.stopRequested = true;
    const queue = getQueue();
    if (queue) {
      queue.paused = true;
      saveQueue(queue);
    }
    setStatus(message, 'warning');
  }

  function deleteQueue() {
    removeStored(KEY.queue);
    state.processing = false;
  }

  function loggedIn() {
    return !document.querySelector('a[href^="/login"], a[href*="/login?"]');
  }

  function selectedRecordsForActiveTab() {
    const records = state.scan?.[state.activeTab] || [];
    return records.filter((record) => state.selected.has(`${state.activeTab}:${record.id}`));
  }

  function actionLabel(action) {
    return action === 'unfollow' ? 'フォロー解除' : 'フォローバック';
  }

  async function startSelectedAction() {
    if (!state.ownerAccount) {
      setStatus('自分のクリエイターページを開いて再読み込みしてください', 'error');
      return;
    }
    if (!isOwnerAccount(state.scan?.account)) {
      setStatus(`他人のアカウントは調査専用です。操作できるのは自分のID（@${state.ownerAccount}）だけです`, 'error');
      return;
    }
    if (!scanIsComplete()) {
      setStatus('完全な調査結果がないため実行できません', 'error');
      return;
    }
    if (!loggedIn()) {
      setStatus('noteへログインしてから実行してください', 'error');
      return;
    }

    const action = state.activeTab === 'followingOnly' ? 'unfollow' : 'follow';
    const records = selectedRecordsForActiveTab()
      .filter((record) => !state.protectedIds.has(record.id));
    if (!records.length) {
      setStatus('実行する相手を選択してください', 'warning');
      return;
    }

    const batchInput = state.shadow.querySelector('#km-batch-size');
    const requested = Math.max(1, Math.min(APP.maxBatch, Number(batchInput?.value || 10)));
    const batch = records.slice(0, requested);
    const names = batch.slice(0, 8).map((record) => `・${record.name}（@${record.id}）`).join('\n');
    const rest = batch.length > 8 ? `\nほか ${batch.length - 8}人` : '';
    const message = `操作対象：@${state.account}\n${actionLabel(action)}を ${batch.length}人に実行します。\n\n${names}${rest}\n\nよろしいですか？`;
    if (!window.confirm(message)) return;

    const queue = queueForAction(action, batch);
    state.stopRequested = false;
    saveQueue(queue);
    setStatus(`${actionLabel(action)}を開始します`, 'warning');
    await processQueue();
  }

  function findRowForId(kind, id) {
    const heading = headingForKind(document, kind);
    const section = heading?.closest('section') || null;
    const list = profileListInSection(section);
    if (!list) return null;
    return Array.from(list.children).find((row) => {
      return profileIdFromRow(row) === id;
    }) || null;
  }

  async function confirmUnfollowDialogIfNeeded() {
    await sleep(500);
    const dialogs = Array.from(document.querySelectorAll('[role="dialog"], dialog')).filter(visible);
    for (const dialog of dialogs) {
      const candidates = Array.from(dialog.querySelectorAll('button')).filter(visible);
      const confirmButton = candidates.find((button) => {
        const text = (button.textContent || '').trim().replace(/\s+/g, '');
        if (!text || text.includes('キャンセル')) return false;
        return text.includes('解除') || text.includes('フォローをやめ');
      });
      if (confirmButton) {
        confirmButton.click();
        return true;
      }
    }
    return false;
  }

  async function waitForPressedState(row, expected, timeoutMs = 8000) {
    const started = Date.now();
    while (Date.now() - started < timeoutMs) {
      if (!row.isConnected) return expected === false;
      const button = row.querySelector('button[aria-pressed], button[data-name="ToggleButton"]');
      if (button?.getAttribute('aria-pressed') === String(expected)) return true;
      await sleep(300);
    }
    return false;
  }

  async function executeCurrentItem(queue, item) {
    const row = findRowForId(queue.kind, item.id);
    if (!row) return { status: 'failed', reason: '対象がこのページに見つかりません' };
    const button = row.querySelector('button[aria-pressed], button[data-name="ToggleButton"]');
    if (!button) return { status: 'failed', reason: '操作ボタンが見つかりません' };

    const pressed = button.getAttribute('aria-pressed') === 'true';
    if (queue.action === 'follow' && pressed) return { status: 'skipped', reason: 'すでにフォロー中' };
    if (queue.action === 'unfollow' && !pressed) return { status: 'skipped', reason: 'すでに解除済み' };

    button.scrollIntoView({ behavior: 'smooth', block: 'center' });
    await sleep(350);
    button.click();
    if (queue.action === 'unfollow') await confirmUnfollowDialogIfNeeded();

    const expected = queue.action === 'follow';
    const verified = await waitForPressedState(row, expected);
    if (!verified) return { status: 'failed', reason: '変更結果を確認できませんでした' };
    return { status: 'completed', reason: '' };
  }

  async function processQueue() {
    if (state.processing) return;
    const queue = getQueue();
    if (!queue || queue.paused) return;
    if (!isOwnerAccount(queue.account)) {
      queue.paused = true;
      saveQueue(queue);
      const ownerLabel = state.ownerAccount ? `@${state.ownerAccount}` : '未確認';
      setStatus(`安全のため停止しました。自分のnote IDは${ownerLabel}です`, 'error');
      return;
    }
    if (!loggedIn()) {
      stopQueue('ログアウト状態のため処理を停止しました');
      return;
    }

    state.processing = true;
    state.stopRequested = false;
    state.minimized = false;
    render();

    try {
      while (queue.index < queue.items.length && !queue.paused && !state.stopRequested) {
        const item = queue.items[queue.index];
        const wantedPath = `/${queue.account}/${queue.kind}`;
        const wantedPage = item.page || 1;
        if (location.pathname !== wantedPath || currentPageNumber() !== wantedPage) {
          saveQueue(queue);
          location.href = listUrl(queue.account, queue.kind, wantedPage);
          return;
        }

        setStatus(`${actionLabel(queue.action)} ${queue.index + 1}/${queue.items.length}：${item.name}`, 'warning');
        const outcome = await executeCurrentItem(queue, item);
        queue.results.push({
          id: item.id,
          name: item.name,
          at: nowIso(),
          ...outcome,
        });
        queue.index += 1;
        if (state.stopRequested) queue.paused = true;
        saveQueue(queue);
        render();

        if (queue.index < queue.items.length && !queue.paused && !state.stopRequested) {
          await sleep(randomBetween(APP.actionDelayMin, APP.actionDelayMax));
        }
      }

      if (queue.index >= queue.items.length) {
        const completed = queue.results.filter((result) => result.status === 'completed').length;
        const skipped = queue.results.filter((result) => result.status === 'skipped').length;
        const failed = queue.results.filter((result) => result.status === 'failed').length;
        writeJson(KEY.lastLog, { ...queue, finishedAt: nowIso() });
        deleteQueue();
        state.scan = null;
        removeStored(KEY.scan);
        state.selected.clear();
        setStatus(`完了：成功 ${completed}／変更済み ${skipped}／失敗 ${failed}。もう一度調査してください`, failed ? 'warning' : 'success');
      }
    } catch (error) {
      stopQueue(`処理エラー：${error.message}`);
    } finally {
      state.processing = false;
      render();
    }
  }

  function toggleAllVisible() {
    if (!state.scan || !actionsAllowed()) return;
    const records = state.scan[state.activeTab] || [];
    const available = records.filter((record) => !state.protectedIds.has(record.id));
    const keys = available.map((record) => `${state.activeTab}:${record.id}`);
    const allSelected = keys.length > 0 && keys.every((key) => state.selected.has(key));
    for (const key of keys) {
      if (allSelected) state.selected.delete(key);
      else state.selected.add(key);
    }
    render();
  }

  function toggleProtected(id) {
    if (state.protectedIds.has(id)) state.protectedIds.delete(id);
    else state.protectedIds.add(id);
    for (const prefix of ['followingOnly', 'followerOnly']) state.selected.delete(`${prefix}:${id}`);
    saveProtected();
    render();
  }

  function exportCsv() {
    if (!state.scan) return;
    const partial = scanIsPartial(state.scan);
    const followingLabel = partial ? 'フォロー側のみ（公開範囲・参考）' : '解除候補';
    const followerLabel = partial ? 'フォロワー側のみ（公開範囲・参考）' : 'フォロバ漏れ';
    const rows = [
      ['区分', '表示名', 'note ID', 'URL', '一覧ページ', '保護'],
      ...state.scan.followingOnly.map((record) => [followingLabel, record.name, record.id, record.url, record.page, state.protectedIds.has(record.id) ? '保護' : '']),
      ...state.scan.followerOnly.map((record) => [followerLabel, record.name, record.id, record.url, record.page, state.protectedIds.has(record.id) ? '保護' : '']),
    ];
    const csv = rows.map((row) => row.map((cell) => `"${String(cell).replaceAll('"', '""')}"`).join(',')).join('\r\n');
    const blob = new Blob([`\uFEFF${csv}`], { type: 'text/csv;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement('a');
    anchor.href = url;
    anchor.download = `note-follow-diff-${state.account}-${new Date().toISOString().slice(0, 10)}.csv`;
    anchor.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  function listCountText(list) {
    const shown = list?.records?.length || 0;
    const total = list?.total || list?.expected || shown;
    return list?.publiclyCapped || total > shown ? `${shown}/${total}` : String(shown);
  }

  function scanSummaryHtml() {
    if (!state.scan) {
      return '<div class="empty">まだ調査していません</div>';
    }
    const date = new Date(state.scan.scannedAt).toLocaleString('ja-JP');
    const partial = scanIsPartial(state.scan);
    return `
      <div class="summary-grid">
        <div><span>フォロー中</span><strong>${escapeHtml(listCountText(state.scan.followings))}</strong></div>
        <div><span>フォロワー</span><strong>${escapeHtml(listCountText(state.scan.followers))}</strong></div>
        <div><span>相互</span><strong>${state.scan.mutual.length}</strong></div>
        <div><span>${partial ? '公開差分' : '差分'}</span><strong>${state.scan.followingOnly.length + state.scan.followerOnly.length}</strong></div>
      </div>
      ${partial ? '<div class="scope-note">公開される先頭1,000人までの比較です。全体の一致・不一致は判定できません。</div>' : ''}
      <div class="scan-date">調査：${escapeHtml(date)}${state.scan.complete ? '' : partial ? '（公開上限・参考値）' : '（不完全）'}</div>
    `;
  }

  function resultListHtml() {
    if (!state.scan) return '';
    const records = state.scan[state.activeTab] || [];
    if (!records.length) return '<div class="empty good">この区分は0人です</div>';
    const selectable = actionsAllowed(state.scan);

    return `<div class="result-list">${records.map((record) => {
      const key = `${state.activeTab}:${record.id}`;
      const protectedUser = state.protectedIds.has(record.id);
      return `
        <div class="result-row ${protectedUser ? 'is-protected' : ''}">
          <label class="check-wrap">
            <input type="checkbox" data-key="${escapeHtml(key)}" ${state.selected.has(key) ? 'checked' : ''} ${protectedUser || !selectable ? 'disabled' : ''}>
          </label>
          <a href="${escapeHtml(record.url)}" target="_blank" rel="noopener">
            <strong>${escapeHtml(record.name)}</strong>
            <span>@${escapeHtml(record.id)} ・ p${record.page}</span>
          </a>
          <button class="protect" data-protect="${escapeHtml(record.id)}">${protectedUser ? '保護中' : '保護'}</button>
        </div>
      `;
    }).join('')}</div>`;
  }

  function queueHtml() {
    const queue = getQueue();
    if (!queue) return '';
    const percent = queue.items.length ? Math.round((queue.index / queue.items.length) * 100) : 0;
    return `
      <div class="queue-box">
        <div><strong>${queue.paused ? '停止中' : escapeHtml(actionLabel(queue.action))}</strong> ${queue.index}/${queue.items.length}</div>
        <div class="bar"><i style="width:${percent}%"></i></div>
        <button id="${queue.paused ? 'km-clear-queue' : 'km-stop-queue'}">${queue.paused ? '停止中の処理を破棄' : '処理を停止'}</button>
      </div>
    `;
  }

  function panelHtml() {
    const followingOnlyCount = state.scan?.followingOnly?.length || 0;
    const followerOnlyCount = state.scan?.followerOnly?.length || 0;
    const activeCount = state.scan?.[state.activeTab]?.length || 0;
    const selectedCount = selectedRecordsForActiveTab().length;
    const actionText = state.activeTab === 'followingOnly' ? '選択した相手を解除' : '選択した相手をフォロー';
    const partial = scanIsPartial(state.scan);
    const ownerKnown = validAccount(state.ownerAccount);
    const ownerMode = isOwnerAccount(state.account);
    const canAct = actionsAllowed(state.scan);
    const followingTabText = partial ? 'フォロー側のみ*' : '解除候補';
    const followerTabText = partial ? 'フォロワー側のみ*' : 'フォロバ漏れ';
    const actionNote = !ownerKnown
      ? '自分のクリエイターページを開いて再読み込みしてください'
      : !ownerMode
        ? '他人のアカウントは調査・CSV専用です'
        : partial
          ? '公開上限による参考値のため操作できません'
          : '実行前に対象を確認し、4〜7秒間隔で処理します';
    const modeText = !ownerKnown
      ? '自分のnote IDを確認できていません'
      : ownerMode
        ? `@${state.ownerAccount}：自分のアカウント（調査＋操作）`
        : '他人のアカウント：調査専用';
    const progress = state.progress
      ? `${state.progress.kind === 'followings' ? 'フォロー中' : 'フォロワー'} ${state.progress.page}/${state.progress.pages || '?'}ページ`
      : '';
    const defaultStatus = ownerKnown
      ? '調査だけならフォロー状態は変わりません'
      : '自分のクリエイターページから開始してください';

    return `
      <button id="km-toggle" class="floating" title="${escapeHtml(APP.name)}">
        黒${followingOnlyCount + followerOnlyCount ? `<span>${followingOnlyCount + followerOnlyCount}</span>` : ''}
      </button>
      <section class="panel ${state.minimized ? 'hidden' : ''}">
        <header class="titlebar">
          <div><strong>黒峰 note整理</strong><small>v${APP.version}</small></div>
          <button id="km-minimize" aria-label="閉じる">−</button>
        </header>
        <div class="body">
          <label class="account-label">note ID
            <input id="km-account" value="${escapeHtml(state.account)}" placeholder="自分または調査するnote ID" inputmode="latin" autocomplete="off">
          </label>
          <div class="mode-badge ${ownerMode ? 'owner' : 'readonly'}">
            ${escapeHtml(modeText)}
          </div>
          <button id="km-scan" class="primary" ${state.busy || state.processing ? 'disabled' : ''}>
            ${state.busy ? '調査中…' : '差分を調査'}
          </button>
          ${progress ? `<div class="progress-text">${escapeHtml(progress)}</div>` : ''}
          <div class="status ${escapeHtml(state.statusType)}">${escapeHtml(state.status || defaultStatus)}</div>
          ${queueHtml()}
          ${scanSummaryHtml()}
          <div class="tabs">
            <button data-tab="followingOnly" class="${state.activeTab === 'followingOnly' ? 'active danger' : ''}">${followingTabText} <b>${followingOnlyCount}</b></button>
            <button data-tab="followerOnly" class="${state.activeTab === 'followerOnly' ? 'active follow' : ''}">${followerTabText} <b>${followerOnlyCount}</b></button>
          </div>
          ${state.scan ? `
            <div class="tools">
              <button id="km-toggle-all" ${canAct ? '' : 'disabled'}>全選択／解除</button>
              <button id="km-export">CSV</button>
              <span>${selectedCount}/${activeCount}選択</span>
            </div>
          ` : ''}
          ${resultListHtml()}
          ${state.scan ? `
            <div class="execute-row">
              <label>1回
                <input id="km-batch-size" type="number" min="1" max="${APP.maxBatch}" value="10" ${canAct ? '' : 'disabled'}>
                人まで
              </label>
              <button id="km-execute" class="execute ${state.activeTab === 'followingOnly' ? 'danger-bg' : 'follow-bg'}" ${!canAct || state.processing ? 'disabled' : ''}>${escapeHtml(actionText)}</button>
            </div>
            <p class="note">${escapeHtml(actionNote)}</p>
          ` : ''}
        </div>
      </section>
    `;
  }

  function bindEvents() {
    const q = (selector) => state.shadow.querySelector(selector);
    q('#km-toggle')?.addEventListener('click', () => {
      state.minimized = false;
      render();
    });
    q('#km-minimize')?.addEventListener('click', () => {
      state.minimized = true;
      render();
    });
    q('#km-scan')?.addEventListener('click', startScan);
    q('#km-account')?.addEventListener('change', (event) => {
      const nextAccount = normalizeAccount(event.target.value);
      if (nextAccount !== state.account) {
        state.scan = null;
        state.selected.clear();
      }
      state.account = nextAccount;
      saveSettings();
      render();
    });
    q('#km-toggle-all')?.addEventListener('click', toggleAllVisible);
    q('#km-export')?.addEventListener('click', exportCsv);
    q('#km-execute')?.addEventListener('click', startSelectedAction);
    q('#km-stop-queue')?.addEventListener('click', () => stopQueue());
    q('#km-clear-queue')?.addEventListener('click', () => {
      deleteQueue();
      setStatus('停止中の処理を破棄しました', 'normal');
    });

    for (const button of state.shadow.querySelectorAll('[data-tab]')) {
      button.addEventListener('click', () => {
        state.activeTab = button.dataset.tab;
        render();
      });
    }
    for (const input of state.shadow.querySelectorAll('input[data-key]')) {
      input.addEventListener('change', () => {
        if (input.checked) state.selected.add(input.dataset.key);
        else state.selected.delete(input.dataset.key);
        render();
      });
    }
    for (const button of state.shadow.querySelectorAll('[data-protect]')) {
      button.addEventListener('click', () => toggleProtected(button.dataset.protect));
    }
  }

  function render() {
    if (!state.shadow) return;
    state.shadow.querySelector('#km-app').innerHTML = panelHtml();
    bindEvents();
  }

  function mount() {
    const host = document.createElement('div');
    host.id = 'km-note-sync-host';
    document.documentElement.appendChild(host);
    const shadow = host.attachShadow({ mode: 'open' });
    shadow.innerHTML = `
      <style>
        :host { all: initial; }
        * { box-sizing: border-box; }
        button, input { font: inherit; }
        button { cursor: pointer; }
        button:disabled { cursor: not-allowed; opacity: .48; }
        .floating {
          position: fixed; right: 14px; bottom: 14px; z-index: 2147483646;
          width: 48px; height: 48px; border: 0; border-radius: 50%; color: #fff;
          background: #161616; box-shadow: 0 8px 24px rgba(0,0,0,.28); font: 800 16px/1 system-ui;
        }
        .floating span {
          position: absolute; right: -4px; top: -5px; min-width: 21px; height: 21px;
          padding: 0 5px; border-radius: 11px; background: #dc2626; color: #fff;
          font: 700 11px/21px system-ui;
        }
        .panel {
          position: fixed; right: 14px; bottom: 72px; z-index: 2147483647;
          width: min(390px, calc(100vw - 20px)); max-height: min(760px, calc(100vh - 95px));
          display: flex; flex-direction: column; overflow: hidden; border: 1px solid #d4d4d4;
          border-radius: 15px; color: #202124; background: #fff;
          box-shadow: 0 16px 50px rgba(0,0,0,.28); font: 14px/1.45 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        }
        .panel.hidden { display: none; }
        .titlebar { display: flex; align-items: center; justify-content: space-between; padding: 11px 12px; color: #fff; background: #171717; }
        .titlebar strong { font-size: 15px; }
        .titlebar small { margin-left: 7px; color: #bdbdbd; }
        .titlebar button { width: 30px; height: 28px; border: 0; border-radius: 7px; color: #fff; background: #343434; font-size: 19px; }
        .body { overflow: auto; overscroll-behavior: contain; padding: 12px; }
        .account-label { display: grid; grid-template-columns: 58px 1fr; align-items: center; gap: 7px; color: #555; font-weight: 700; }
        .account-label input { min-width: 0; height: 37px; padding: 0 10px; border: 1px solid #c9c9c9; border-radius: 8px; color: #111; background: #fff; }
        .mode-badge { margin-top: 6px; padding: 5px 8px; border-radius: 7px; font-size: 11px; font-weight: 700; }
        .mode-badge.owner { color: #166534; background: #dcfce7; }
        .mode-badge.readonly { color: #92400e; background: #fef3c7; }
        .primary { width: 100%; margin-top: 9px; padding: 10px; border: 0; border-radius: 9px; color: #fff; background: #171717; font-weight: 800; }
        .progress-text { margin-top: 8px; color: #555; text-align: center; font-size: 12px; }
        .status { margin-top: 8px; padding: 8px 9px; border-radius: 8px; color: #4b5563; background: #f3f4f6; font-size: 12px; }
        .status.success { color: #166534; background: #dcfce7; }
        .status.error { color: #991b1b; background: #fee2e2; }
        .status.warning { color: #92400e; background: #fef3c7; }
        .summary-grid { display: grid; grid-template-columns: repeat(4,1fr); gap: 6px; margin-top: 10px; }
        .summary-grid div { padding: 8px 4px; border: 1px solid #e5e7eb; border-radius: 8px; text-align: center; }
        .summary-grid span { display: block; color: #6b7280; font-size: 10px; }
        .summary-grid strong { display: block; margin-top: 2px; font-size: 18px; }
        .scope-note { margin-top: 7px; padding: 7px 8px; border-radius: 7px; color: #92400e; background: #fef3c7; font-size: 11px; }
        .scan-date { margin: 5px 2px 0; color: #8a8a8a; text-align: right; font-size: 10px; }
        .tabs { display: grid; grid-template-columns: 1fr 1fr; gap: 6px; margin-top: 10px; }
        .tabs button { padding: 9px 4px; border: 1px solid #d1d5db; border-radius: 8px; color: #4b5563; background: #fff; font-weight: 700; }
        .tabs button.active.danger { border-color: #dc2626; color: #991b1b; background: #fef2f2; }
        .tabs button.active.follow { border-color: #16a34a; color: #166534; background: #f0fdf4; }
        .tabs b { display: inline-block; min-width: 20px; margin-left: 3px; padding: 1px 5px; border-radius: 10px; color: inherit; background: rgba(0,0,0,.07); }
        .tools { display: flex; align-items: center; gap: 6px; margin-top: 8px; }
        .tools button, .protect { border: 1px solid #d1d5db; border-radius: 7px; color: #374151; background: #fff; }
        .tools button { padding: 6px 8px; font-size: 11px; }
        .tools span { margin-left: auto; color: #777; font-size: 11px; }
        .result-list { max-height: 285px; margin-top: 7px; overflow: auto; border: 1px solid #e5e7eb; border-radius: 9px; }
        .result-row { display: grid; grid-template-columns: 25px minmax(0,1fr) auto; align-items: center; gap: 6px; min-height: 54px; padding: 7px; border-bottom: 1px solid #eee; }
        .result-row:last-child { border-bottom: 0; }
        .result-row.is-protected { background: #f7f7f7; opacity: .78; }
        .check-wrap { display: grid; place-items: center; }
        .check-wrap input { width: 18px; height: 18px; accent-color: #171717; }
        .result-row a { min-width: 0; color: #111827; text-decoration: none; }
        .result-row a strong { display: block; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; font-size: 12px; }
        .result-row a span { display: block; overflow: hidden; color: #6b7280; text-overflow: ellipsis; white-space: nowrap; font-size: 11px; }
        .protect { padding: 5px 6px; font-size: 10px; }
        .empty { margin-top: 9px; padding: 18px 8px; border: 1px dashed #d1d5db; border-radius: 9px; color: #777; text-align: center; }
        .empty.good { color: #166534; background: #f0fdf4; }
        .execute-row { display: grid; grid-template-columns: auto 1fr; align-items: center; gap: 7px; margin-top: 9px; }
        .execute-row label { color: #555; font-size: 11px; }
        .execute-row input { width: 43px; padding: 6px 3px; border: 1px solid #d1d5db; border-radius: 6px; text-align: center; }
        .execute { min-height: 38px; border: 0; border-radius: 8px; color: #fff; font-weight: 800; }
        .danger-bg { background: #b91c1c; }
        .follow-bg { background: #15803d; }
        .note { margin: 6px 0 0; color: #888; text-align: right; font-size: 10px; }
        .queue-box { margin-top: 8px; padding: 9px; border: 1px solid #f59e0b; border-radius: 8px; background: #fffbeb; }
        .queue-box div:first-child { font-size: 12px; }
        .queue-box .bar { height: 6px; margin-top: 6px; overflow: hidden; border-radius: 4px; background: #fde68a; }
        .queue-box .bar i { display: block; height: 100%; background: #d97706; }
        .queue-box button { margin-top: 7px; padding: 5px 8px; border: 1px solid #d97706; border-radius: 6px; color: #92400e; background: #fff; font-size: 11px; }
        @media (max-width: 640px) {
          .floating { right: 10px; bottom: calc(10px + env(safe-area-inset-bottom)); }
          .panel { right: 7px; bottom: calc(66px + env(safe-area-inset-bottom)); width: calc(100vw - 14px); max-height: calc(100dvh - 82px - env(safe-area-inset-bottom)); border-radius: 13px; }
          .result-list { max-height: 34dvh; }
        }
      </style>
      <div id="km-app"></div>
    `;
    state.root = host;
    state.shadow = shadow;
    render();
  }

  function boot() {
    loadState();
    mount();
    const queue = getQueue();
    if (queue && !queue.paused) {
      state.minimized = false;
      setTimeout(processQueue, 900);
    }
  }

  // Pure helpers are exposed read-only for local verification and future maintenance.
  Object.defineProperty(window, '__KM_NOTE_SYNC_INTERNALS__', {
    configurable: true,
    value: Object.freeze({
      version: APP.version,
      normalizeAccount,
      profileAccountFromPath,
      ownerAccountFromDocument,
      profileIdFromHref,
      profileIdFromRow,
      compareLists,
      uniqueRecords,
      parseListDocument,
      queueForAction,
      isOwnerAccount,
      actionsAllowed,
    }),
  });

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot, { once: true });
  else boot();
})();
