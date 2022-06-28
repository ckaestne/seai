//add own markdown extensions
//needs to insert mymarkdown between marked.js and markdown.js
const pathMD = deps[1].src.replace("plugin/markdown/markdown.js","_assets/_assets/plugin/mymarkdown.js")
const pathFitty = deps[1].src.replace("plugin/markdown/markdown.js","_assets/_assets/plugin/fitty.min.js")
deps.splice(1,0,{src:pathMD})
deps.push({src:pathFitty})
console.log(deps)
