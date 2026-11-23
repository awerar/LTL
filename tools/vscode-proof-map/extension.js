// Proof Map: a VS Code front end to tools/proof-map.
//
// All analysis stays in the Python script; this extension runs
// `tools/proof-map json` and shows the result as a tree under the root (or,
// in users mode, the definitions that use a given one), lists of what to
// review next top down and bottom up, a status bar summary and CodeLenses in
// Agda files. Ticking a checkbox runs `proof-map done` or `undo`. Saving an Agda
// file re-runs Agda; ledger changes only re-read the last generated HTML
// (--cached). Calls to the script run one at a time.

const vscode = require('vscode');
const cp = require('child_process');
const path = require('path');

const SEP = '\u0000';

let output;
let data = null;            // the parsed JSON, or null before the first run
let folder = null;          // the workspace folder holding tools/proof-map

// ---------------------------------------------------------------------------
// Running the script

let queue = Promise.resolve();

function run(args) {
  const config = vscode.workspace.getConfiguration('proofMap');
  const script = path.resolve(folder, config.get('command'));
  const job = queue.then(() => new Promise((resolve, reject) => {
    cp.execFile(script, args, { cwd: folder, maxBuffer: 64 << 20 },
      (err, stdout, stderr) => {
        if (stderr.trim()) output.appendLine(stderr.trim());
        if (err) reject(new Error(stderr.trim() || err.message));
        else resolve(stdout);
      });
  }));
  queue = job.catch(() => {});
  return job;
}

// Coalesces refreshes: a full run (Agda) wins over a cached one.
let pending = null;
let pendingFull = false;
let listeners = [];

function refresh(full) {
  pendingFull = pendingFull || full;
  if (pending) return pending;
  pending = new Promise(resolve => setTimeout(resolve, 300)).then(async () => {
    const args = pendingFull ? [] : ['--cached'];
    pending = null;
    pendingFull = false;
    try {
      data = JSON.parse(await run([...args, 'json', currentRoot()]));
      if (data.agdaError) {
        output.appendLine('Agda failed; showing the last checked state.');
      }
    } catch (e) {
      output.appendLine(String(e.message || e));
      vscode.window.showErrorMessage(`Proof Map: ${firstLine(e.message)}`,
        'Show Output').then(c => c && output.show());
    }
    listeners.forEach(f => f());
  });
  return pending;
}

function firstLine(s) {
  return String(s || '').split('\n').find(l => l.trim()) || 'failed';
}

async function mark(qnames, done, note) {
  if (!qnames.length) return;
  const args = ['--cached', done ? 'done' : 'undo', ...qnames];
  if (done && note) args.push('-m', note);
  try {
    await run(args);
  } catch (e) {
    vscode.window.showErrorMessage(`Proof Map: ${firstLine(e.message)}`);
  }
  await refresh(false);
}

// ---------------------------------------------------------------------------
// State

let state;                  // context.workspaceState

function currentRoot() {
  return state.get('root') ||
    vscode.workspace.getConfiguration('proofMap').get('root');
}

function openOnly() {
  return state.get('openOnly', false);
}

// In users mode the tree shows who uses this definition, upwards.
function usersOf() {
  const qn = state.get('usersOf');
  return qn && def(qn) ? qn : null;
}

function def(qn) {
  return data && data.defs[qn];
}

function stripLine(name) {
  return name.replace(/@\d+$/, '');
}

// The line (0-based) of a definition in an open document. The stored line
// comes from the last successful Agda run, so if the text there does not
// start the definition, the nearest line that does is used.
function locate(doc, d) {
  const name = stripLine(d.name);
  // A module application is named `open M` after the module it applies.
  const applied = name.startsWith('open ') && name.slice(5);
  const starts = i => {
    const t = doc.lineAt(i).text.trimStart()
      .replace(/^(data|record|pattern)\s+/, '');
    if (applied) {
      return /^(open|module)\s/.test(t) &&
        new RegExp(`(^|[\\s.])${applied.replace(/\W/g, '\\$&')}(\\s|$)`).test(t);
    }
    return t.startsWith(name) &&
      (t.length === name.length || /[\s:]/.test(t[name.length]));
  };
  const want = Math.min(Math.max(d.line - 1, 0), doc.lineCount - 1);
  if (starts(want)) return want;
  for (let k = 1; k < doc.lineCount; k++) {
    if (want - k >= 0 && starts(want - k)) return want - k;
    if (want + k < doc.lineCount && starts(want + k)) return want + k;
  }
  return want;
}

async function openDef(qn) {
  const d = def(qn);
  if (!d) return;
  const doc = await vscode.workspace.openTextDocument(
    vscode.Uri.file(path.join(folder, d.path)));
  const line = locate(doc, d);
  const range = new vscode.Range(line, 0, line, 0);
  await vscode.window.showTextDocument(doc,
    { selection: range, preview: true });
}

// ---------------------------------------------------------------------------
// Tree items

const ICON = {
  stale: new vscode.ThemeIcon('warning',
    new vscode.ThemeColor('list.warningForeground')),
  complete: new vscode.ThemeIcon('pass-filled',
    new vscode.ThemeColor('testing.iconPassed')),
};

function moduleShort(d) {
  return d.module.replace(/^LTL\./, '');
}

function tooltip(d) {
  const md = new vscode.MarkdownString();
  md.appendMarkdown(`**${d.name}**  \n\`${d.path}:${d.line}\`\n\n`);
  if (d.status === 'done') {
    md.appendMarkdown(`Reviewed ${d.reviewed.date}`);
  } else if (d.status === 'stale') {
    md.appendMarkdown(`Changed since its review on ${d.reviewed.date}`);
  } else {
    md.appendMarkdown('Not reviewed');
  }
  if (d.reviewed && d.reviewed.note) md.appendText(`: ${d.reviewed.note}`);
  md.appendMarkdown(`\n\n${d.open} open below, uses ${d.uses.length}, ` +
    `used by ${d.usedBy.length}`);
  if (d.library.length) md.appendText(`\nlibrary: ${d.library.join(' ')}`);
  return md;
}

function treeItem(el, description) {
  const d = def(el.qn);
  const recursive = el.path.indexOf(el.qn) < el.path.length - 1;
  const kids = !el.flat && !recursive && children(el).length > 0;
  const item = new vscode.TreeItem(d.name,
    !kids ? vscode.TreeItemCollapsibleState.None
      : el.path.length === 1 ? vscode.TreeItemCollapsibleState.Expanded
        : vscode.TreeItemCollapsibleState.Collapsed);
  item.id = (el.flat ? 'next-' + el.flat : 'tree') + SEP + el.path.join(SEP);
  item.description = description !== undefined ? description
    : (recursive ? '↻ ' : '') +
      (!usersOf() && d.open && d.uses.length ? `${d.open} open · ` : '') +
      moduleShort(d);
  item.tooltip = tooltip(d);
  item.checkboxState = d.status === 'done'
    ? vscode.TreeItemCheckboxState.Checked
    : vscode.TreeItemCheckboxState.Unchecked;
  if (d.status === 'stale') item.iconPath = ICON.stale;
  else if (d.open === 0 && d.uses.length) item.iconPath = ICON.complete;
  item.contextValue = 'def';
  item.command = { command: 'proofMap.open', title: 'Open', arguments: [el.qn] };
  return item;
}

function children(el) {
  const d = def(el.qn);
  if (!d || el.path.indexOf(el.qn) < el.path.length - 1) return [];
  if (usersOf()) return d.usedBy.filter(def);
  return d.uses.filter(c => {
    const e = def(c);
    return e && !(openOnly() && e.status === 'done' && e.open === 0);
  });
}

function treeRoot() {
  return usersOf() || data.root;
}

class TreeProvider {
  constructor() {
    this.emitter = new vscode.EventEmitter();
    this.onDidChangeTreeData = this.emitter.event;
  }
  getTreeItem(el) { return treeItem(el); }
  getChildren(el) {
    if (!data) return [];
    if (!el) return def(treeRoot()) ? [{ qn: treeRoot(), path: [treeRoot()] }] : [];
    return children(el).map(c => ({ qn: c, path: [...el.path, c] }));
  }
  getParent(el) {
    if (el.path.length < 2) return undefined;
    const p = el.path.slice(0, -1);
    return { qn: p[p.length - 1], path: p };
  }
  // The shortest path from the root to qn through visible children.
  pathTo(qn) {
    if (!data) return null;
    const prev = new Map([[treeRoot(), null]]);
    const todo = [treeRoot()];
    while (todo.length) {
      const k = todo.shift();
      if (k === qn) {
        const p = [];
        for (let x = k; x !== null; x = prev.get(x)) p.unshift(x);
        return { qn, path: p };
      }
      for (const c of children({ qn: k, path: [k] })) {
        if (!prev.has(c)) { prev.set(c, k); todo.push(c); }
      }
    }
    return null;
  }
}

// The definitions to review next: top down, those with a reviewed user;
// bottom up, those whose uses are all reviewed. The script groups them by
// branch (the children of the root, heaviest first) and orders each branch
// so that a subtree is finished before the next. A branch is shown as its
// own item, holding the rest of its group; the first one starts expanded.
class NextProvider {
  constructor(up) {
    this.up = up;
    this.dir = up ? 'up' : 'down';
    this.emitter = new vscode.EventEmitter();
    this.onDidChangeTreeData = this.emitter.event;
  }
  getTreeItem(el) {
    const d = def(el.qn);
    let desc;
    if (this.up) {
      desc = `${d.above} above · ` + (d.uses.length
        ? `uses ${d.uses.length}, all reviewed · ${moduleShort(d)}` : moduleShort(d));
    } else {
      const by = d.usedBy.filter(u => def(u) && def(u).status === 'done')
        .map(u => def(u).name);
      desc = `${d.open} open below · ` +
        (by.length ? `used by ${by.join(', ')}` : moduleShort(d));
    }
    if (el.group) desc = `${el.group.length} next · ${d.open} open below`;
    const item = treeItem(el, desc);
    if (el.group && el.group.length) {
      item.collapsibleState = el.first
        ? vscode.TreeItemCollapsibleState.Expanded
        : vscode.TreeItemCollapsibleState.Collapsed;
    }
    return item;
  }
  getChildren(el) {
    if (!data) return [];
    if (el) {
      return (el.group || []).map(qn => ({ qn, path: [el.qn, qn], flat: this.dir }));
    }
    const groups = data.branches
      .map(b => ({ branch: b.branch, items: b[this.dir].filter(def) }))
      .filter(b => b.items.length && def(b.branch));
    return groups.map((b, i) => {
      const rest = b.items.filter(qn => qn !== b.branch);
      return rest.length
        ? { qn: b.branch, path: [b.branch], flat: this.dir, group: rest, first: i === 0 }
        : { qn: b.branch, path: [b.branch], flat: this.dir };
    });
  }
}

// ---------------------------------------------------------------------------
// Explorer decorations: per Agda file (and folder), a badge with the number
// of open definitions, ✓ when all are reviewed (green) and ~ when some
// changed since their review (yellow). Partly reviewed files get no colour,
// so git's colours still show. Leaf modules have no tracked definitions and
// get nothing.

class Decorations {
  constructor() {
    this.emitter = new vscode.EventEmitter();
    this.onDidChangeFileDecorations = this.emitter.event;
  }
  provideFileDecoration(uri) {
    if (!data || uri.scheme !== 'file' ||
        !vscode.workspace.getConfiguration('proofMap').get('explorerBadges')) {
      return undefined;
    }
    const rel = path.relative(folder, uri.fsPath).split(path.sep).join('/');
    if (!rel || rel.startsWith('..')) return undefined;
    const isFile = rel.endsWith('.agda');
    const defs = Object.values(data.defs)
      .filter(d => isFile ? d.path === rel : d.path.startsWith(rel + '/'));
    if (!defs.length) return undefined;
    const done = defs.filter(d => d.status === 'done').length;
    const stale = defs.filter(d => d.status === 'stale').length;
    const open = defs.length - done;
    const where = isFile ? '' : ' in this folder';
    const tooltip = `Proof Map: ${done === defs.length ? `all ${defs.length}` : `${done}/${defs.length}`}` +
      ` reviewed${where}` + (stale ? ` · ${stale} changed since review` : '');
    if (stale) {
      return new vscode.FileDecoration('~', tooltip,
        new vscode.ThemeColor('list.warningForeground'));
    }
    if (!open) {
      return new vscode.FileDecoration('✓', tooltip,
        new vscode.ThemeColor('testing.iconPassed'));
    }
    return new vscode.FileDecoration(open > 99 ? '9+' : String(open), tooltip);
  }
}

// The path from the configured root down to the focused branch, by names.
function breadcrumb() {
  if (!data || !state.get('root')) return null;
  const want = vscode.workspace.getConfiguration('proofMap').get('root');
  const top = Object.keys(data.defs).find(k => {
    const d = data.defs[k];
    return d.name === want || k === want || k.endsWith('.' + want);
  });
  if (!top || top === data.root) return null;
  const prev = new Map([[data.root, null]]);
  const todo = [data.root];
  while (todo.length) {
    const k = todo.shift();
    if (k === top) {
      const names = [];
      for (let x = k; x !== null; x = prev.get(x)) names.push(def(x).name);
      return names.join(' › ');
    }
    for (const u of def(k).usedBy) {
      if (def(u) && !prev.has(u)) { prev.set(u, k); todo.push(u); }
    }
  }
  return null;
}

// ---------------------------------------------------------------------------
// CodeLenses

class Lenses {
  constructor() {
    this.emitter = new vscode.EventEmitter();
    this.onDidChangeCodeLenses = this.emitter.event;
  }
  provideCodeLenses(doc) {
    if (!data || !vscode.workspace.getConfiguration('proofMap').get('codeLens')) {
      return [];
    }
    const rel = path.relative(folder, doc.uri.fsPath).split(path.sep).join('/');
    const lenses = [];
    // At the top of the file: how much of it is reviewed, and a way to mark
    // (or, once complete, unmark) all of it.
    const inFile = Object.values(data.defs).filter(d => d.path === rel);
    if (inFile.length) {
      const done = inFile.filter(d => d.status === 'done').length;
      const top = new vscode.Range(0, 0, 0, 0);
      lenses.push(new vscode.CodeLens(top, done < inFile.length
        ? { title: `$(checklist) ${done}/${inFile.length} reviewed in this file · mark all`,
            command: 'proofMap.markFile', arguments: [{ file: rel }] }
        : { title: `$(pass-filled) all ${inFile.length} reviewed in this file`,
            tooltip: 'Remove the marks of this file', command: 'proofMap.unmarkFile',
            arguments: [{ file: rel }] }));
    }
    for (const [qn, d] of Object.entries(data.defs)) {
      if (d.path !== rel) continue;
      const range = new vscode.Range(locate(doc, d), 0, locate(doc, d), 0);
      const title = d.status === 'done' ? `$(pass) reviewed ${d.reviewed.date}`
        : d.status === 'stale' ? '$(warning) changed since review'
          : '$(circle-large-outline) not reviewed';
      lenses.push(new vscode.CodeLens(range,
        { title, command: 'proofMap.toggleReview', arguments: [qn] }));
      const below = d.open && d.uses.length ? ` · ${d.open} open below` : '';
      const where = d.belowRoot ? '' : ' · not under the root';
      lenses.push(new vscode.CodeLens(range, {
        title: `uses ${d.uses.length}${below}${where}`,
        tooltip: 'Reveal in the tree',
        command: 'proofMap.reveal', arguments: [qn],
      }));
      lenses.push(new vscode.CodeLens(range, {
        title: `used by ${d.usedBy.length}`,
        tooltip: 'Show the definitions that use this one',
        command: 'proofMap.showUsers', arguments: [qn],
      }));
    }
    return lenses;
  }
}

// ---------------------------------------------------------------------------
// Activation

function activate(context) {
  folder = (vscode.workspace.workspaceFolders || [])
    .map(f => f.uri.fsPath)
    .find(f => require('fs').existsSync(path.join(f, 'tools', 'proof-map')));
  if (!folder) return;
  state = context.workspaceState;
  output = vscode.window.createOutputChannel('Proof Map');

  const tree = new TreeProvider();
  const next = new NextProvider(false);
  const nextUp = new NextProvider(true);
  const lenses = new Lenses();
  const decorations = new Decorations();
  const treeView = vscode.window.createTreeView('proofMap.tree',
    { treeDataProvider: tree, manageCheckboxStateManually: true, showCollapseAll: true });
  const nextView = vscode.window.createTreeView('proofMap.next',
    { treeDataProvider: next, manageCheckboxStateManually: true });
  const nextUpView = vscode.window.createTreeView('proofMap.nextUp',
    { treeDataProvider: nextUp, manageCheckboxStateManually: true });
  const status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 50);
  status.command = 'proofMap.tree.focus';

  const setContext = () => {
    vscode.commands.executeCommand('setContext', 'proofMap.openOnly', openOnly());
    vscode.commands.executeCommand('setContext', 'proofMap.customRoot',
      !!state.get('root') || !!state.get('usersOf'));
    vscode.commands.executeCommand('setContext', 'proofMap.focused', !!state.get('root'));
  };
  setContext();

  listeners.push(() => {
    tree.emitter.fire();
    next.emitter.fire();
    nextUp.emitter.fire();
    lenses.emitter.fire();
    decorations.emitter.fire(undefined);
    if (!data) return;
    const below = Object.values(data.defs).filter(d => d.belowRoot);
    const done = below.filter(d => d.status === 'done').length;
    const stale = below.filter(d => d.status === 'stale').length;
    const focus = state.get('root') && def(data.root) ? def(data.root).name : null;
    status.text = `${data.agdaError ? '$(warning)' : '$(checklist)'} ` +
      `${done}/${below.length} reviewed${focus ? ` in ${focus}` : ''}` +
      `${stale ? ` · ${stale} stale` : ''}`;
    for (const v of [treeView, nextView, nextUpView]) {
      v.description = focus ? `focus: ${focus}` : undefined;
    }
    // While focused, the status bar takes you to the focused definition.
    status.command = focus ? 'proofMap.goToFocus' : 'proofMap.tree.focus';
    const gap = data.between.length
      ? `\n${data.between.length} open between reviewed definitions` : '';
    status.tooltip = data.agdaError
      ? `Agda failed; showing the last checked state.\n\n${firstLine(data.agdaError)}`
      : `Proof Map: definitions under ${def(data.root) ? def(data.root).name : data.root}${gap}` +
        (focus ? `\nClick to go to ${focus}.` : '');
    status.show();
    const crumb = breadcrumb();
    treeView.message = [
      data.agdaError && 'Agda failed: showing the last checked state (see Output → Proof Map).',
      usersOf() && `Definitions that use ${def(usersOf()).name}, upwards.`,
      !usersOf() && crumb && `Focused on ${crumb}.`,
    ].filter(Boolean).join(' ') || undefined;
    nextView.message = nextUpView.message = crumb ? `Only within ${crumb}.` : undefined;
  });

  const onCheck = e => {
    const done = [], undo = [];
    for (const [el, s] of e.items) {
      (s === vscode.TreeItemCheckboxState.Checked ? done : undo).push(el.qn);
    }
    mark(done, true).then(() => mark(undo, false));
  };

  // The definition at the cursor: the last one starting at or above it.
  const atCursor = () => {
    const ed = vscode.window.activeTextEditor;
    if (!ed || !data) return null;
    const rel = path.relative(folder, ed.document.uri.fsPath).split(path.sep).join('/');
    const line = ed.selection.active.line;
    let best = null;
    for (const [k, d] of Object.entries(data.defs)) {
      if (d.path !== rel) continue;
      const at = locate(ed.document, d);
      if (at <= line && (!best || at > best.at)) best = { k, at };
    }
    return best && best.k;
  };

  // From a tree item, a CodeLens (a name) or the editor (nothing).
  const target = arg => (arg && arg.qn) || (typeof arg === 'string' && arg) || atCursor();

  // The Agda file meant: from the explorer or an editor title (a Uri), a
  // tree item (its definition's file), a CodeLens ({ file }) or the editor.
  const fileOf = arg => {
    let p = null;
    if (arg instanceof vscode.Uri) p = arg.fsPath;
    else if (arg && arg.qn && def(arg.qn)) return def(arg.qn).path;
    else if (arg && arg.file) return arg.file;
    else if (vscode.window.activeTextEditor) {
      p = vscode.window.activeTextEditor.document.uri.fsPath;
    }
    return p && p.endsWith('.agda')
      ? path.relative(folder, p).split(path.sep).join('/') : null;
  };

  const markFile = async arg => {
    const rel = fileOf(arg);
    if (!rel || !data) return;
    const fresh = Object.entries(data.defs)
      .filter(([, d]) => d.path === rel && d.status !== 'done').map(([k]) => k);
    if (!fresh.length) {
      vscode.window.showInformationMessage(`Proof Map: everything in ${rel} is already reviewed.`);
      return;
    }
    try {
      await run(['--cached', 'done', rel]);
    } catch (e) {
      vscode.window.showErrorMessage(`Proof Map: ${firstLine(e.message)}`);
      return;
    }
    await refresh(false);
    vscode.window.showInformationMessage(
      `Proof Map: marked ${fresh.length} definition${fresh.length > 1 ? 's' : ''} in ${rel} as reviewed.`,
      'Undo').then(c => c && mark(fresh, false));
  };

  const unmarkFile = async arg => {
    const rel = fileOf(arg);
    if (!rel || !data) return;
    const marked = Object.values(data.defs).filter(d => d.path === rel && d.reviewed);
    if (!marked.length) return;
    const ok = await vscode.window.showWarningMessage(
      `Remove the ${marked.length} review mark${marked.length > 1 ? 's' : ''} in ${rel}?`,
      { modal: true }, 'Remove');
    if (ok !== 'Remove') return;
    try {
      await run(['--cached', 'undo', rel]);
    } catch (e) {
      vscode.window.showErrorMessage(`Proof Map: ${firstLine(e.message)}`);
    }
    await refresh(false);
  };

  const showUsers = async arg => {
    const qn = target(arg);
    if (!qn) return;
    await state.update('usersOf', qn);
    setContext();
    listeners.forEach(f => f());
    await vscode.commands.executeCommand('proofMap.tree.focus');
  };

  const reveal = async arg => {
    const qn = target(arg);
    if (!qn) return;
    if (usersOf() && !tree.pathTo(qn)) {
      await state.update('usersOf', undefined);
      setContext();
      listeners.forEach(f => f());
    }
    const el = tree.pathTo(qn);
    if (!el) {
      vscode.window.showInformationMessage(
        `Proof Map: ${def(qn) ? def(qn).name : qn} is not under the current root` +
        (openOnly() ? ' (or is hidden as reviewed)' : '') + '.');
      return;
    }
    await treeView.reveal(el, { select: true, focus: false, expand: false });
  };

  const sub = (...ds) => context.subscriptions.push(...ds);
  sub(treeView, nextView, nextUpView, status, output,
    treeView.onDidChangeCheckboxState(onCheck),
    nextView.onDidChangeCheckboxState(onCheck),
    nextUpView.onDidChangeCheckboxState(onCheck),
    vscode.window.registerFileDecorationProvider(decorations),
    vscode.languages.registerCodeLensProvider(
      [{ language: 'agda', scheme: 'file' }, { pattern: '**/*.agda', scheme: 'file' }],
      lenses),
    vscode.commands.registerCommand('proofMap.refresh', () => refresh(true)),
    vscode.commands.registerCommand('proofMap.open', openDef),
    vscode.commands.registerCommand('proofMap.showOpenOnly', async () => {
      await state.update('openOnly', true); setContext(); listeners.forEach(f => f());
    }),
    vscode.commands.registerCommand('proofMap.showAll', async () => {
      await state.update('openOnly', false); setContext(); listeners.forEach(f => f());
    }),
    // Focus on a branch: from a tree item, or the definition at the cursor.
    vscode.commands.registerCommand('proofMap.setRoot', async arg => {
      const qn = target(arg);
      if (!qn) return;
      await state.update('usersOf', undefined);
      await state.update('root', qn); setContext(); await refresh(false);
      await vscode.commands.executeCommand('proofMap.tree.focus');
    }),
    vscode.commands.registerCommand('proofMap.resetRoot', async () => {
      await state.update('usersOf', undefined);
      await state.update('root', undefined); setContext(); await refresh(false);
    }),
    vscode.commands.registerCommand('proofMap.showUsers', showUsers),
    vscode.commands.registerCommand('proofMap.goToFocus', () => data && openDef(data.root)),
    vscode.commands.registerCommand('proofMap.markFile', markFile),
    vscode.commands.registerCommand('proofMap.unmarkFile', unmarkFile),
    vscode.commands.registerCommand('proofMap.markWithNote', async el => {
      const d = def(el.qn);
      const note = await vscode.window.showInputBox({
        prompt: `Review note for ${d.name}`,
        value: d.reviewed ? d.reviewed.note : '',
      });
      if (note !== undefined) await mark([el.qn], true, note);
    }),
    vscode.commands.registerCommand('proofMap.toggleReview', qn => {
      const d = def(qn);
      if (d) return mark([qn], d.status !== 'done');
    }),
    vscode.commands.registerCommand('proofMap.reveal', reveal),
    vscode.workspace.onDidSaveTextDocument(doc => {
      if (doc.fileName.endsWith('.agda')) refresh(true);
    }),
    vscode.workspace.onDidChangeConfiguration(e => {
      if (e.affectsConfiguration('proofMap')) refresh(false);
    }),
  );
  const ledger = vscode.workspace.createFileSystemWatcher(
    new vscode.RelativePattern(folder, 'docs/review.tsv'));
  sub(ledger, ledger.onDidChange(() => refresh(false)),
    ledger.onDidCreate(() => refresh(false)),
    ledger.onDidDelete(() => refresh(false)));

  refresh(true);
  // For the tests in test/.
  return { refresh, mark, reveal, showUsers, markFile, unmarkFile, tree, next, nextUp, lenses, treeView,
    setFocus: qn => vscode.commands.executeCommand('proofMap.setRoot', { qn }),
    decorations,
    nextView,
    get data() { return data; } };
}

function deactivate() {}

module.exports = { activate, deactivate };
