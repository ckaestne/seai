echo generate main html page in _site/
# prepare
mkdir _site
cd lectures
npm install
cd ..

# gen index.hmtl
cp .assets/template.html _site/index.html
lectures/node_modules/marked/bin/marked -i README.md >> _site/index.html
cat .assets/template_end.html >> _site/index.html
cp *.png _site/
cp *.jpg _site/

# gen slides
cd lectures
npm run generate
cp -r _static/ ../_site/slides
cd ..
