import test from 'node:test';
import assert from 'node:assert/strict';
import {readJSON,extract,validate,claimHash,evidenceHash} from '../scripts/core.mjs';
const data=readJSON('content/paper.json');
test('pinned source, every claim, proof partition and dependency verify',()=>{
 const result=validate(data);assert.equal(result.nodes,18);assert.equal(result.pending.length,0);
});
test('a changed source span is rejected rather than silently quoted',()=>{
 const anchor={...data.nodes[0].statement,end:data.nodes[0].statement.end-1};
 assert.throws(()=>extract(anchor),/Stale anchor/);
});
test('an uncited claim cannot enter the build',()=>{
 const altered=structuredClone(data);altered.nodes[0].summary[0].cites=[];
 assert.throws(()=>validate(altered),/Uncited claim/);
});
test('an edited claim invalidates its audit verdict',()=>{
 const altered=structuredClone(data);altered.nodes[0].summary[0].text+=' Changed.';
 assert.equal(validate(altered).pending.length,1);
});
test('proof cuts cannot drop a source character',()=>{
 const altered=structuredClone(data);const node=altered.nodes.find(n=>n.steps.length);
 node.steps[0].end--;assert.throws(()=>validate(altered),/Gap\/overlap|Incomplete proof/);
});
test('a reversed dependency creating a cycle is rejected',()=>{
 const altered=structuredClone(data);const node=altered.nodes.find(n=>n.uses.length);
 const dependency=altered.nodes.find(n=>n.id===node.uses[0].id);
 dependency.uses.push({id:node.id,cite:node.statement,why:node.title});
 assert.throws(()=>validate(altered),/Dependency cycle/);
});
test('public release remains blocked without author approval',()=>{
 assert.throws(()=>validate(data,{release:true}),/author-approval|author approval|ENOENT/);
});
