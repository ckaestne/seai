//add own markdown extensions
console.log("loading markdown extensions")
const pathMD = deps[1].src.replace("plugin/markdown/markdown.js","_assets/_assets/plugin/mymarkdown.js")
const pathFitty = deps[1].src.replace("plugin/markdown/markdown.js","_assets/_assets/plugin/fitty.min.js")
deps.splice(2,0,{src:pathMD})
deps.push({src:pathFitty})
console.log(pathMD)
console.log(deps)
