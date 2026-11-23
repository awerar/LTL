// Drives the extension inside VS Code and writes a report to
// $PROOF_MAP_TEST_OUT. Run from the repository root (a window opens briefly;
// docs/review.tsv is restored afterwards):
//
//   PROOF_MAP_TEST_OUT=/tmp/proof-map-test.txt code --user-data-dir /tmp/pm-user \
//     --extensions-dir /tmp/pm-ext --extensionDevelopmentPath=$PWD/tools/vscode-proof-map \
//     --extensionTestsPath=$PWD/tools/vscode-proof-map/test/suite.js $PWD

const vscode = require('vscode');
const assert = require('assert');
const fs = require('fs');
const path = require('path');

exports.run = async () => {
  const out = [];
  const log = s => out.push(s);
  const folder = vscode.workspace.workspaceFolders[0].uri.fsPath;
  const ledger = path.join(folder, 'docs', 'review.tsv');
  const before = fs.existsSync(ledger) ? fs.readFileSync(ledger, 'utf8') : null;
  let failed = false;
  try {
    const ext = vscode.extensions.all.find(e => e.packageJSON.name === 'proof-map');
    const api = await ext.activate();
    await api.refresh(true);
    const data = api.data;
    assert(data && data.defs[data.root], 'no data for the root');
    log(`root ${data.root}; ${Object.keys(data.defs).length} definitions; agdaError ${!!data.agdaError}`);

    // The tree: root, its children, and every node reachable by expanding.
    const [root] = api.tree.getChildren();
    const it = api.tree.getTreeItem(root);
    log(`root item: ${it.label} | ${it.description} | checkbox ${it.checkboxState} | collapsible ${it.collapsibleState}`);
    log('children: ' + api.tree.getChildren(root).map(k => api.tree.getTreeItem(k).label).join(', '));
    const seen = new Set();
    const ids = new Set();
    const walk = el => {
      const item = api.tree.getTreeItem(el);
      assert(!ids.has(item.id), `duplicate id ${item.id}`);
      ids.add(item.id);
      if (seen.has(el.qn)) return;
      seen.add(el.qn);
      for (const c of api.tree.getChildren(el)) walk(c);
    };
    walk(root);
    const below = Object.values(api.data.defs).filter(d => d.belowRoot).length;
    log(`expanded ${seen.size} distinct definitions (belowRoot: ${below}), ${ids.size} items`);
    assert.strictEqual(seen.size, below);

    // CodeLenses land on the line that starts each definition.
    const files = [...new Set(Object.values(data.defs).map(d => d.path))];
    let total = 0;
    const off = [];
    for (const f of files) {
      const uri = vscode.Uri.file(path.join(folder, f));
      const doc = await vscode.workspace.openTextDocument(uri);
      const lenses = await vscode.commands.executeCommand('vscode.executeCodeLensProvider', uri);
      for (const l of lenses.filter(l => l.command && l.command.command === 'proofMap.toggleReview')) {
        total++;
        const d = api.data.defs[l.command.arguments[0]];
        const text = doc.lineAt(l.range.start.line).text.trim().replace(/^(data|record|pattern)\s+/, '');
        const name = d.name.replace(/@\d+$/, '');
        const ok = name.startsWith('open ')
          ? /^(open|module)\s/.test(text) && text.includes(name.slice(5))
          : text.startsWith(name);
        if (!ok) {
          off.push(`${f}:${l.range.start.line + 1} ${d.name}: "${text.slice(0, 50)}"`);
        }
      }
    }
    log(`lenses: ${total} in ${files.length} files; not on the definition's line: ${off.length}`);
    off.slice(0, 15).forEach(s => log('  ' + s));

    // Marking, the next list, toggling and revealing.
    await api.mark([data.root], true, 'extension test');
    assert.strictEqual(api.data.defs[data.root].status, 'done');
    log('after mark: root checkbox ' + api.tree.getTreeItem(api.tree.getChildren()[0]).checkboxState +
      '; next: ' + api.next.getChildren().map(e => api.next.getTreeItem(e).label + ' (' +
        api.next.getTreeItem(e).description + ')').join(', '));
    await vscode.commands.executeCommand('proofMap.toggleReview', data.root);
    log('after toggle: ' + api.data.defs[data.root].status);
    assert.strictEqual(api.data.defs[data.root].status, 'open');

    const deep = Object.keys(api.data.defs).find(k => api.data.defs[k].name === 'sccGraph');
    await vscode.commands.executeCommand('proofMap.tree.focus');
    await api.reveal(deep);
    log('revealed: ' + api.treeView.selection.map(e =>
      e.path.map(q => api.data.defs[q].name).join(' > ')).join(' | '));
    assert.strictEqual(api.treeView.selection.length, 1);

    await vscode.commands.executeCommand('proofMap.showOpenOnly');
    await vscode.commands.executeCommand('proofMap.showAll');

    // Bottom up, and where the two directions meet.
    const val = Object.keys(api.data.defs).find(k => api.data.defs[k].name === 'Val');
    const upBefore = api.nextUp.getChildren().length;
    await api.mark([data.root, val], true);
    const up = api.nextUp.getChildren().map(e => api.nextUp.getTreeItem(e));
    log(`bottom up: ${upBefore} before, ${up.length} after marking Val; first: ` +
      up.slice(0, 3).map(i => `${i.label} (${i.description})`).join(', '));
    const weights = api.data.frontierUp.map(k => api.data.defs[k].above);
    assert(weights.every((w, i) => i === 0 || weights[i - 1] >= w), 'bottom up not ranked');
    const opens = api.data.frontier.map(k => api.data.defs[k].open);
    assert(opens.every((w, i) => i === 0 || opens[i - 1] >= w), 'top down not ranked');
    log('top down: ' + api.next.getChildren().slice(0, 3).map(e =>
      `${api.next.getTreeItem(e).label} (${api.next.getTreeItem(e).description})`).join(', '));
    log(`between: ${api.data.between.length}`);
    assert(api.data.between.length > 0, 'nothing between root and Val');
    assert(!api.data.frontierUp.includes(val));

    // Users mode: the tree shows who uses closure, upwards.
    const closure = Object.keys(api.data.defs).find(k => api.data.defs[k].name === 'closure');
    await api.showUsers(closure);
    const [top] = api.tree.getChildren();
    log(`users of ${api.tree.getTreeItem(top).label}: ` +
      api.tree.getChildren(top).map(k => api.tree.getTreeItem(k).label).join(', ') +
      ` | message: ${api.treeView.message}`);
    assert.strictEqual(top.qn, closure);
    await vscode.commands.executeCommand('proofMap.resetRoot');
    assert.strictEqual(api.tree.getChildren()[0].qn, data.root);
    await api.mark([data.root, val], false);

    // Branch groups hold exactly the next list.
    for (const [name, prov, list] of [['down', api.next, api.data.frontier],
      ['up', api.nextUp, api.data.frontierUp]]) {
      const tops = prov.getChildren();
      const all = tops.flatMap(t => [t.qn, ...prov.getChildren(t).map(c => c.qn)]);
      const listed = new Set(list);
      const extra = all.filter(q => !listed.has(q));   // reviewed branch headers
      assert(extra.every(q => api.data.defs[q].status === 'done' ||
        api.data.branches.some(b => b.branch === q)), `${name}: stray items`);
      assert(list.every(q => all.includes(q)), `${name}: items missing from groups`);
      log(`${name} groups: ` + tops.map(t => `${api.data.defs[t.qn].name}` +
        (t.group ? ` (+${t.group.length})` : '')).join(', '));
    }

    // Focus on a branch: the lists stay inside it, with a breadcrumb.
    const pscc = Object.keys(api.data.defs).find(k => api.data.defs[k].name === 'provableSCC');
    await api.setFocus(pscc);
    assert.strictEqual(api.data.root, pscc);
    assert(api.data.frontier.every(k => api.data.defs[k].belowRoot));
    log(`focus: ${api.treeView.message} | next: ${api.nextView.message} | ` +
      `${api.data.frontier.length} next, ${api.data.frontierUp.length} bottom up`);
    assert(/decideCorrect › decide › provableSCC/.test(api.treeView.message));
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    await vscode.commands.executeCommand('proofMap.goToFocus');
    const ed0 = vscode.window.activeTextEditor;
    const went = ed0 && `${path.relative(folder, ed0.document.uri.fsPath)}:${ed0.selection.active.line + 1}`;
    log(`go to focus: ${went}: ${ed0 && ed0.document.lineAt(ed0.selection.active.line).text.trim().slice(0, 40)}`);
    assert(ed0 && ed0.document.lineAt(ed0.selection.active.line).text.startsWith('provableSCC'));
    await vscode.commands.executeCommand('proofMap.resetRoot');
    assert.strictEqual(api.data.root, data.root);

    // The same from the editor: the definition at the cursor.
    const d = api.data.defs[pscc];
    const ed = await vscode.window.showTextDocument(
      await vscode.workspace.openTextDocument(path.join(folder, d.path)));
    const at = new vscode.Position(d.line, 0);   // the line after its signature
    ed.selection = new vscode.Selection(at, at);
    await vscode.commands.executeCommand('proofMap.setRoot');
    log(`focus from the editor at ${d.path}:${d.line + 1}: ${api.data.defs[api.data.root].name}`);
    assert.strictEqual(api.data.root, pscc);
    await vscode.commands.executeCommand('proofMap.resetRoot');

    // A whole file: marked, its top CodeLens, then the Undo path.
    const barFile = 'LTL/Lib/Bar.agda';
    const inBar = () => Object.entries(api.data.defs).filter(([, d]) => d.path === barFile);
    const fresh = inBar().filter(([, d]) => d.status !== 'done').map(([k]) => k);
    await api.markFile({ file: barFile });
    assert(inBar().every(([, d]) => d.status === 'done'), 'file not fully marked');
    const barUri = vscode.Uri.file(path.join(folder, barFile));
    const barLenses = await vscode.commands.executeCommand('vscode.executeCodeLensProvider', barUri);
    const topLens = barLenses.find(l => l.range.start.line === 0 && l.command);
    log(`file ${barFile}: ${inBar().length} definitions marked; top lens: ${topLens && topLens.command.title}`);
    assert(topLens && topLens.command.command === 'proofMap.unmarkFile');
    await api.mark(fresh, false);
    assert(inBar().every(([k, d]) => fresh.includes(k) ? d.status !== 'done' : true));
    log(`after undo: ${inBar().filter(([, d]) => d.status === 'done').length} marked`);
  } catch (e) {
    failed = true;
    log('FAIL ' + (e.stack || e));
  } finally {
    if (before === null) fs.rmSync(ledger, { force: true });
    else fs.writeFileSync(ledger, before);
    log(failed ? 'RESULT: failed' : 'RESULT: passed');
    fs.writeFileSync(process.env.PROOF_MAP_TEST_OUT, out.join('\n') + '\n');
  }
};
