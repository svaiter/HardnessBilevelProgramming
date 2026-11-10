import path from 'node:path';
import {execFileSync} from 'node:child_process';
import {root} from './core.mjs';
for(const[script,args]of [['sync-lean.mjs',process.argv.slice(2)],['export.mjs',[]]])
 if(script!=='export.mjs'||!process.argv.includes('--help'))execFileSync(process.execPath,[path.join(root,'scripts',script),...args],{stdio:'inherit'});
