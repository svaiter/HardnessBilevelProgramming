import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {execFileSync} from 'node:child_process';
import {codeHash,indexLean,resolveMappings,readWorkingSnapshot,readGitSnapshot} from '../scripts/lean-sources.mjs';

const original='namespace Demo\nsection\n/-- A result. -/\ntheorem result : True := by trivial\nend\nend Demo\n';
const mapping={nodes:{result:{file:'Main.lean',declaration:'Demo.result',status:'formalized'}}};
const baseline={files:{'Main.lean':codeHash(original)}};
test('comments, including nested comments and apparent declarations, are ignored',()=>{
 const text='/- namespace False /- theorem result : False := by sorry -/ -/\n'+original;
 assert.deepEqual(indexLean('Main.lean',text).map(d=>d.declaration),['Demo.result']);
 assert.equal(codeHash(text),codeHash(original));
});
test('namespace, section, noncomputable section, and qualified names resolve',()=>{
 const text='namespace Demo\nnoncomputable section\ndef Child.x := 1\nend\nnamespace Child\nprotected theorem yes : True := by trivial\nend Child\nend Demo\n';
 assert.deepEqual(indexLean('X.lean',text).map(d=>d.declaration),['Demo.Child.x','Demo.Child.yes']);
});
test('comment and line shifts refresh links without declaring a semantic change',()=>{
 const text='-- inserted comment\n\n'+original;
 const result=resolveMappings({'Main.lean':text},mapping,baseline);
 assert.equal(result.nodes.result.line,6);assert.equal(result.nodes.result.status,'formalized');assert.deepEqual(result.changedFiles,[]);
});
test('a unique declaration moved to another file is located automatically',()=>{
 const result=resolveMappings({'Moved.lean':original},mapping,baseline);
 assert.equal(result.nodes.result.file,'Moved.lean');assert.equal(result.issues.length,0);
});
test('changed source or dependencies invalidates green badges conservatively',()=>{
 const result=resolveMappings({'Main.lean':original.replace('True','False')},mapping,baseline);
 assert.equal(result.nodes.result.status,'source-changed');
 assert.equal(resolveMappings({'Main.lean':original,'Other.lean':'def value := 2'},mapping,baseline).nodes.result.status,'source-changed');
});
test('a removed or ambiguous declaration is not silently linked elsewhere',()=>{
 assert.equal(resolveMappings({'Main.lean':'-- theorem result : True := by trivial'},mapping,baseline).nodes.result.status,'unresolved');
 const result=resolveMappings({'First.lean':original,'Second.lean':original},mapping,baseline);
 assert.equal(result.issues[0].reason,'ambiguous');
});
test('string contents remain significant to change detection',()=>{
 assert.notEqual(codeHash('def s := "a b"'),codeHash('def s := "a  b"'));
});
test('working tree includes edits and new Lean files; commit snapshots remain immutable',()=>{
 const repo=fs.mkdtempSync(path.join(os.tmpdir(),'visual-paper-git-'));
 const git=(...args)=>execFileSync('git',['-C',repo,...args],{encoding:'utf8',stdio:['ignore','pipe','pipe']});
 try{
  git('init');fs.writeFileSync(path.join(repo,'Main.lean'),original);git('add','Main.lean');
  git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-m','fixture');
  assert.equal(readWorkingSnapshot(repo).dirty,false);
  fs.writeFileSync(path.join(repo,'Main.lean'),'-- moved line\n'+original);
  fs.writeFileSync(path.join(repo,'New.lean'),'def added := 1\n');
  const current=readWorkingSnapshot(repo);assert.equal(current.dirty,true);assert.ok(current.files['New.lean']);
  assert.equal(readGitSnapshot(repo,'HEAD').files['Main.lean'],original);
  fs.rmSync(path.join(repo,'Main.lean'));assert.ok(!('Main.lean' in readWorkingSnapshot(repo).files));
 }finally{fs.rmSync(repo,{recursive:true,force:true});}
});
