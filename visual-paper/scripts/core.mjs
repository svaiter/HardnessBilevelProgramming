import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {fileURLToPath} from 'node:url';

export const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
export const sha = s => crypto.createHash('sha256').update(s).digest('hex');
export const readJSON = p => JSON.parse(fs.readFileSync(path.join(root,p),'utf8'));
const sourceCache = new Map();
export function sourcePath(file) {
  const mapped = file.startsWith('../') ? 'source/repository/'+file.slice(3) : file;
  const absolute = path.resolve(root,mapped);
  if (!absolute.startsWith(root+path.sep)) throw Error('Source outside pinned tree: '+file);
  return absolute;
}
export function source(file) {
  if (!sourceCache.has(file)) sourceCache.set(file, fs.readFileSync(sourcePath(file),'utf8'));
  return sourceCache.get(file);
}
export function extract(a) {
  if (!a || typeof a.file!=='string' || !Number.isInteger(a.start) || !Number.isInteger(a.end)) throw Error('Invalid source anchor');
  const chars=Array.from(source(a.file));
  if(a.start<0||a.end<=a.start||a.end>chars.length)throw Error('Anchor out of range: '+a.file);
  const text=chars.slice(a.start,a.end).join('');
  if(sha(text)!==a.sha256)throw Error('Stale anchor: '+a.file+':'+a.start);
  return text;
}
export function walk(value,fn,location='') {
  if(!value||typeof value!=='object')return;
  fn(value,location);
  for(const[k,v]of Object.entries(value))if(v&&typeof v==='object')walk(v,fn,location+'.'+k);
}
export function claimsIn(data) {
  const claims=new Map();
  walk(data,v=>{if(typeof v.text==='string'&&typeof v.id==='string'){
    if(!Array.isArray(v.cites)||!v.cites.length)throw Error('Uncited claim '+v.id);
    if(claims.has(v.id)&&JSON.stringify(claims.get(v.id))!==JSON.stringify(v))throw Error('Conflicting claim id '+v.id);
    claims.set(v.id,v);
  }});
  return [...claims.values()];
}
export function claimHash(c){return sha(c.text);}
export function evidenceHash(c){return sha(c.cites.map(a=>sha(extract(a))).join('\n'));}
export function lineOf(a){return Array.from(source(a.file)).slice(0,a.start).join('').split('\n').length;}
export function sourceURL(a){
 const lock=readJSON('SOURCE.lock');
 if(a.file.startsWith('../'))return `https://github.com/svaiter/HardnessBilevelProgramming/blob/${lock.lean.commit}/${a.file.slice(3)}#L${lineOf(a)}`;
 if(a.file.endsWith('.tex')){
  // Link to a literal prose fragment from the audited span. TeX commands and
  // comments break fragments: joining across them could produce text that does
  // not occur in arXiv's rendered HTML.
  const text=extract(a).replace(/(?<!\\)%[^\n]*/g,' ');
  const candidates=text.split(/\\[a-zA-Z]+\*?(?:\[[^\]]*\])?|[^a-zA-Z0-9\s]|\n\s*\n/)
   .map(s=>s.replace(/\s+/g,' ').trim())
   .filter(s=>s.length>=30 && /[a-zA-Z]{4}/.test(s))
   .sort((a,b)=>b.length-a.length);
  const fragment=candidates[0]?.slice(0,80).replace(/\s+\S*$/, '').trim();
  return 'https://arxiv.org/html/2407.12372v2'+(fragment?'#:~:text='+encodeURIComponent(fragment):'');
 }
 return 'https://arxiv.org/abs/2407.12372v2';
}
export function validate(data,{release=false}={}) {
 const lock=readJSON('SOURCE.lock');
 for(const[file,hash]of Object.entries(lock.files))if(sha(fs.readFileSync(path.join(root,file)))!==hash)throw Error('Pinned source changed: '+file);
 let anchors=0;
 walk(data,v=>{if(v.file&&v.sha256&&Number.isInteger(v.start)){extract(v);anchors++;}});
 const claims=claimsIn(data);
 const ids=new Set(data.nodes.map(n=>n.id));
 if(ids.size!==data.nodes.length)throw Error('Duplicate node id');
 const colors=new Map();
 function visit(id){
  if(colors.get(id)===1)throw Error('Dependency cycle at '+id);
  if(colors.get(id)===2)return;
  colors.set(id,1);const node=data.nodes.find(n=>n.id===id);
  for(const edge of node.uses||[]){if(!ids.has(edge.id))throw Error('Missing dependency '+edge.id);if(edge.id===id)throw Error('Self dependency '+id);extract(edge.cite);visit(edge.id);}
  colors.set(id,2);
 }
 for(const n of data.nodes){
  visit(n.id);
  if(n.proof){
   const proof=extract(n.proof);let position=n.proof.start;let text='';
   for(const step of n.steps||[]){if(step.start!==position||step.end<=step.start)throw Error('Gap/overlap in proof '+n.id);text+=Array.from(source(n.proof.file)).slice(step.start,step.end).join('');position=step.end;}
   if(position!==n.proof.end||text!==proof)throw Error('Incomplete proof partition '+n.id);
  }
  if(n.lean?.file){
   const code=source('../'+n.lean.file);const name=n.lean.declaration?.split('.').at(-1);
   if(!name||!code.includes(name))throw Error('Lean mapping not found '+n.id);
  }
 }
 const ledger=fs.existsSync(path.join(root,'audit/ledger.json'))?readJSON('audit/ledger.json'):[];
 let audited=0;const pending=[];
 for(const c of claims){
  const found=ledger.find(v=>v.id===c.id&&v.claim_hash===claimHash(c)&&v.evidence_hash===evidenceHash(c)&&v.verdict==='supported');
  if(found)audited++;else pending.push(c.id);
 }
 if(release){
  if(pending.length)throw Error('Release blocked: '+pending.length+' unaudited/stale claims');
  const approval=readJSON('audit/author-approval.json');
  if(approval.public_release!==true||approval.content_sha256!==sha(JSON.stringify(data)))throw Error('Release blocked: author approval missing or stale');
  if(!approval.audit_policy_accepted)throw Error('Release blocked: cross-provider audit policy unresolved');
  if((data.figures||[]).some(f=>f.status!=='approved'))throw Error('Release blocked: figures await author approval');
 }
 return {nodes:data.nodes.length,anchors,claims:claims.length,audited,pending,edges:data.nodes.reduce((s,n)=>s+(n.uses||[]).length,0)};
}
