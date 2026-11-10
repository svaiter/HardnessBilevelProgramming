import {readJSON,validate} from './core.mjs';
console.log(JSON.stringify(validate(readJSON('content/paper.json'),{release:process.argv.includes('--release')}),null,2));
