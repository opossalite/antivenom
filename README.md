# Antivenom
Fiber art pattern generator.

## Use

1. Python dependencies: `beautifulsoup4 lxml reportlab`
1. Run the following script for images (press F12, console tab), this will download a .json file:
```
(async () => {
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  const title = document.querySelector('#title-cover')?.innerText.trim() || document.title;
  const photos = {};
  const rows = [...document.querySelectorAll('#ul_main li')].filter(li =>
    /^li\d+$/.test(li.id) && li.querySelector('.cam-icon img[alt="Click to see photo"]'));
  const find = n => document.querySelector(`#ul_main li[data-ext="img"][data-line="${n}"] img`);
  for (const li of rows) {
    const n = li.id.slice(2);
    if (!find(n)) li.querySelector('.cam-icon').click();
    for (let i = 0; i < 40 && !photos[n]; i++) {
      await sleep(200);
      const img = find(n);
      const src = img && (img.dataset.src || img.currentSrc || img.src);
      if (src && !src.startsWith('data:')) photos[n] = src;
    }
    if (!photos[n]) console.warn('no photo captured for line', n);
    await sleep(800 + Math.random() * 1500);   // pause between clicks
  }
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([JSON.stringify({ title, photos }, null, 1)], { type: 'application/json' }));
  a.download = title.replace(/\W+/g, '-').toLowerCase() + '.json';
  a.click();
})();
```

2. Run SingleFile.
3. Put the .html and the .json in the same location, then run this:
```
python antivenom.py "file.html" --photos "file.json" --pdf -o patterns/
```
4. Optional: use `--no-photos --no-photo-markers` if not using photos and only care about text
5. Optional: can remove the `--pdf` flag if a .pdf is not needed

## License
This work is dual-licensed under GPL Version 2 and GPL Version 3. You may choose between these licenses on a case-by-case basis.

