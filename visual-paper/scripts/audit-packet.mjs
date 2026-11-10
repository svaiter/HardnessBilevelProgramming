import fs from 'node:fs';
import path from 'node:path';
import {root,readJSON,extract,claimsIn,sha,claimHash,evidenceHash} from './core.mjs';
const data=readJSON('content/paper.json');const claims=claimsIn(data);
const evidence=new Map();
for(const c of claims)for(const a of c.cites){const key=a.sha256;if(!evidence.has(key))evidence.set(key,{id:key,file:a.file,start:a.start,end:a.end,text:extract(a)});}
const packet=claims.map(c=>({id:c.id,text:c.text,evidence:c.cites.map(a=>a.sha256),claim_hash:claimHash(c),evidence_hash:evidenceHash(c)}));
fs.writeFileSync(path.join(root,'audit/packets/source.json'),JSON.stringify([...evidence.values()],null,2));
fs.writeFileSync(path.join(root,'audit/packets/claims.json'),JSON.stringify(packet,null,2));
fs.writeFileSync(path.join(root,'audit/packets/manifest.json'),JSON.stringify({source_hash:sha(JSON.stringify([...evidence.values()])),claims_hash:sha(JSON.stringify(packet)),count:claims.length},null,2));
console.log(`${claims.length} claims; ${evidence.size} distinct source spans`);
