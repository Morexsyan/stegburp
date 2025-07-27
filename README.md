# stegburp

[![預覽](https://github.com/Morexsyan/stegburp/raw/main/preview.png)](https://github.com/Morexsyan/stegburp/raw/main/test.mp4)


wink wink, it's me.
Thanks for using this tool!

StegBurp is a high-performance brute-force tool designed to crack passwords used with StegSnow, a steganographic utility for hiding messages in ASCII text files.
It supports multithreaded password cracking and is optimized for both speed and compatibility.
idea from SCIST Final CTF.

Have fun!
by syuan
## how 2 use
1. `gcc -O3 -march=x86-64-v2 -o stegburp stegburp.c -pthr`
2. `./stegburp <secret file> <wordlist> keyword:flag{`

like

`./stegburp test.txt /usr/share/wordlists/rockyou.txt keyword:flag{`


