const input = process.argv[2]
const pdffile = process.argv[3]

console.log("printing ", input, " to ", pdffile)


const puppeteer = require('puppeteer');         // include library
const path = require('path');
const fs = require('fs').promises;


const x = path.resolve(input);

const config = "?print-pdf&showNotes=separate-page&pdfMaxPagesPerSlide=1/#"

const url = "file://"+x+config;

function msleep(n) {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, n);
}

(async () => {                                  // declare function
  const browser = await puppeteer.launch({args: ["--no-sandbox","--disable-setuid-sandbox","--disable-dev-shm-usage","--disable-gpu"]});     // run browser
  const page = await browser.newPage();         // create new tab
  var x;
  x= await page.goto(url, { waitUntil: 'load' });  // go to page
  msleep(2000)
  await page.screenshot({path:"x.png"})
  await page.pdf({path: pdffile, width:"14.67 in",height: "8.25 in",margin:{top:0,buttom:0,left:0,right:0}, printBackground: true });                             // generate pdf current page
  await browser.close();                        // close browser


    const buffer = await fs.readFile(pdffile);
    for (const offset of [97, 98, 99, 100, 132, 133, 134, 135]) {
      buffer[offset] = 0;
    }

    await fs.writeFile(pdffile, buffer);
})();

