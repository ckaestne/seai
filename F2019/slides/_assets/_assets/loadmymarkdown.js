//add own markdown extensions
const pathMD = deps[2].src.replace("plugin/markdown/markdown.js","_assets/plugin/mymarkdown.js")
const pathFitty = deps[2].src.replace("plugin/markdown/markdown.js","_assets/plugin/fitty.min.js")
deps.splice(2,0,{src:pathMD})
deps.push({src:pathFitty})
