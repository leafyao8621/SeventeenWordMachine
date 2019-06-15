var change = {
    "registry": false,
    "addr": false,
    "memory": false,
    "cur": false,
    "out": false
}


var memAddr = 0x3000;
var memAddrMask = 0xf;
var memAddrThreshold = 0;
var meta = new Array(1 << 16);
var cur = {};
var out = "";

var [translate, lookup] = (() => {
    var lookup = {
        "0": "零",
        "1": "壱",
        "2": "弐",
        "3": "参",
        "4": "肆",
        "5": "伍",
        "6": "陸",
        "7": "質",
        "8": "捌",
        "9": "玖",
        "a": "甲",
        "b": "乙",
        "c": "丙",
        "d": "丁",
        "e": "戊",
        "f": "己"
    };
    return [
        (v) => {
            return ((v >>> 0) & 0xffff).toString(16).padStart(4, "0").replace(/[0-9a-f]/g, n => lookup[n]);
        },
        (v) => {
            return lookup[v.toString(16)];
        }
    ];
})();

var [translateBin, lookupBin] = (() => {
    var lookup = {
        "0": "陰",
        "1": "陽"
    };
    return [
        (v) => {
            return ((v >>> 0) & 0xffff).toString(2).padStart(16, "0").replace(/[01]/g, n => lookup[n]);
        },
        (v) => {
            return lookup[v.toString(2)];
        }
    ]
})();
var [setPC, getPC, cpuToString, setRegister, getRegister, setCC, getCC,
     setMemory, getMemory, halt, unhalt, getHalt] = (() => { 
    let memory = new Int16Array(1 << 16);
    let halt = 1;
    let cpu = {
        r: new Int16Array(8),
        pc: 0,
        cc: 0
    };
    return [
        (n) => {
            n >>>= 0;
            n &= 0xffff;
            if (n >= 0 && n < (1 << 16)) {
                cpu.pc = n;
            }
        },
        () => {
            return cpu.pc;
        },
        () => {
            return JSON.stringify(cpu);
        },
        (i, n) => {
            cpu.r[i] = n;
        },
        (i) => {
            return cpu.r[i];
        },
        (n) => {
            if (n < 0) {
                cpu.cc = 4;
            } else if (n == 0) {
                cpu.cc = 2;
            } else {
                cpu.cc = 1;
            }
        },
        () => {
            return cpu.cc;
        },
        (i, n) => {
            i >>>= 0;
            i &= 0xffff;
            if (i >= 0 && i < (1 << 16)) {
                memory[i] = n;
            }
        },
        (i) => {
            i >>>= 0;
            i &= 0xffff;
            if (i >= 0 && i < (1 << 16)) {
                return memory[i];
            }
        },
        () => {
            halt = 1;
        },
        () => {
            halt = 0;
        },
        () => {
            return halt;
        }
    ]
})();

function disassemble(i) {
    switch (i & 0xf000) {
    case 1 << 12: //add
        if (i & 0x0020) {
            return `ADD R${(i & 0x0e00) >> 9}, R${(i & 0x01c0) >> 6}, #${((i & 0xf)  - (i & 0x10))}`
        } else {
            return `ADD R${(i & 0x0e00) >> 9}, R${(i & 0x01c0) >> 6}, R${i & 0x7}`
        }
    case 5 << 12: //and
        if (i & 0x0020) {
            return `AND R${(i & 0x0e00) >> 9}, R${(i & 0x01c0) >> 6}, #${((i & 0xf)  - (i & 0x10))}`
        } else {
            return `AND R${(i & 0x0e00) >> 9}, R${(i & 0x01c0) >> 6}, R${i & 0x7}`
        }
    case 9 << 12: //not
        return `NOT R${(i & 0x0e00) >> 9}, R${(i & 0x01c0) >> 6}`;
    case 2 << 12: //ld
        return `LD R${(i & 0x0e00) >> 9}, #${((i & 0xff) - (i & 0x100))}`;
    case 0xa << 12: //ldi
        return `LDI R${(i & 0x0e00) >> 9}, R${((i & 0xff) - (i & 0x100))}`;
    case 6 << 12: //ldr
        return `LDR R${(i & 0x0e00) >> 9}, R${(i & 0x01c0) >> 6}, #${((i & 0x1f) - (i & 0x20))}`;
    case 3 << 12: //st
        return `ST R${(i & 0x0e00) >> 9}, #${((i & 0xff) - (i & 0x100))}`;
    case 0xb << 12: //sti
        return `STI R${(i & 0x0e00) >> 9}, #${((i & 0xff) - (i & 0x100))}`;
    case 7 << 12: //str
        return `STR R${(i & 0x0e00) >> 9}, R${(i & 0x01c0) >> 6}, #${((i & 0x1f) - (i & 0x20))}`;
    case 0: //br
        return `BR${i & 0x800 ? "n" : ""}${i & 0x400 ? "z" : ""}${i & 0x200 ? "p" : ""} #${((i & 0xff) - (i & 0x100))}`
    case 0xc << 12: //jmp ret
        return `JMP R${(i & 0x01c0) >> 6}`
    case 0x4 << 12: //jsr jsrr
        if (i & 0x800) {
            return `JSR #${((i & 0x2ff) - (i & 0x300))}`;
        } else {
            return `JSRR R${(i & 0x1c0) >> 6}`;
        }
    case 0xf << 12: //trap
        return `TRAP #${i & 0xff}`
    }
}

function load() {
    if (code) {
        setPC(code[0].orig);
        for (let i = 0; i < code.length; i++) {
            for (let j = 0; j < code[i].code.length; j++) {
                setMemory(j + code[i].orig, parseInt(code[i].code[j].code, 2));
                meta[j + code[i].orig] = {
                    kana: code[i].code[j].kana,
                    text: code[i].code[j].text
                };
            }
        }
    }
}

function execute(i) {
    switch (i & 0xf000) {
    case 1 << 12: //add
        if (i & 0x0020) {
            setRegister((i & 0x0e00) >> 9,
                        getRegister((i & 0x01c0) >> 6) +
                        ((i & 0xf)  - (i & 0x10)));
        } else {
            setRegister((i & 0x0e00) >> 9,
                        getRegister((i & 0x01c0) >> 6) +
                        getRegister(i & 0x7));
        }
        setCC(getRegister((i & 0x0e00) >> 9));
        break;
    case 5 << 12: //and
        if (i & 0x0020) {
            setRegister((i & 0x0e00) >> 9,
                        getRegister((i & 0x01c0) >> 6) &
                        ((i & 0xf)  - (i & 0x10)));
        } else {
            setRegister((i & 0x0e00) >> 9,
                        getRegister((i & 0x01c0) >> 6) &
                        getRegister(i & 0x7));
        }
        setCC(getRegister((i & 0x0e00) >> 9));
        break;
    case 9 << 12: //not
        setRegister((i & 0x0e00) >> 9,
                    ~getRegister((i & 0x01c0) >> 6));
        setCC(getRegister((i & 0x0e00) >> 9));
        break;
    case 2 << 12: //ld
        setRegister((i & 0x0e00) >> 9,
                    getMemory(getPC() + 1 + ((i & 0xff) - (i & 0x100))));
        setCC(getRegister((i & 0x0e00) >> 9));
        break;
    case 0xa << 12: //ldi
        setRegister((i & 0x0e00) >> 9,
                    getMemory(getMemory(getPC() + 1 + ((i & 0xff) - (i & 0x100)))));
        setCC(getRegister((i & 0x0e00) >> 9));
        break;
    case 6 << 12: //ldr
        setRegister((i & 0x0e00) >> 9,
                    getMemory(getRegister((i & 0x01c0) >> 6) +
                    ((i & 0x1f) - (i & 0x20))));
        setCC(getRegister((i & 0x0e00) >> 9));
        break;
    case 3 << 12: //st
        setMemory(getPC() + 1 + ((i & 0xff) - (i & 0x100)),
                  getRegister((i & 0x0e00) >> 9));
        break;
    case 0xb << 12: //sti
        setMemory(getMemory(getPC() + 1 + ((i & 0xff) - (i & 0x100))),
                  getRegister((i & 0x0e00) >> 9));
        break;
    case 7 << 12: //str
        setMemory((getRegister((i & 0x01c0) >> 6) +
                  ((i & 0x1f) - (i & 0x20))),
                  getRegister((i & 0x0e00) >> 9));
        break;
    case 0: //br
        if (getCC() == ((i & 0xe00) >> 9)) {
            setPC(getPC() + ((i & 0xff) - (i & 0x100)));
        }
        break;
    case 0xc << 12: //jmp ret
        setPC(getRegister((i & 0x01c0) >> 6));
        break;
    case 0x4 << 12: //jsr jsrr
        setRegister(7, getPC());
        if (i & 0x800) {
            setPC(getPC() + ((i & 0x2ff) - (i & 0x300)));
        } else {
            setPC(getRegister((i & 0x1c0) >> 6));
        }
        break;
    case 0xf << 12: //trap
        switch (i & 0xff) {
        case 0x25:
            halt();
            out += "<br>停止</br>";
            break;
        case 0x20:
            out += getRegister(0).toString() + "<br>";
            break;
        case 0x21:
            out += (String.fromCharCode(getMemory(getRegister(0))))
                   .replace(/\n/, "<br>")
                   .replace(/&/, "&amp;")
                   .replace(/</, "&lt;")
                   .replace(/>/, "&gt;")
                   .replace(/"/, "&quot;")
                   .replace(/'/, "&#39;");
            break;
        case 0x22:
            for (let i = getRegister(0); getMemory(i); i++) {
                out += (String.fromCharCode(getMemory(i)))
                       .replace(/&/, "&amp;")
                       .replace(/</, "&lt;")
                       .replace(/>/, "&gt;")
                       .replace(/"/, "&quot;")
                       .replace(/'/, "&#39;")
                       .replace(/\n/, "<br>");
            }
            break;
        }
    }
}

function step() {
    if (!getHalt()) {
        let out = {
            "hex": translate((getMemory(getPC()) >>> 0) & 0xffff),
            "bin": translateBin((getMemory(getPC()) >>> 0) & 0xffff),
            "asm": disassemble(getMemory(getPC())),
            "kana": meta[getPC()].kana,
            "text":meta[getPC()].text
        }
        execute(getMemory(getPC()));
        setPC(getPC() + 1);
        return out;
    }
}

function run() {
    for (; !getHalt(); setPC(getPC() + 1)) {
        execute(getMemory(getPC()));
    }
}

var code = null;


function setMemAddr(v) {
    memAddr &= ~memAddrMask;
    memAddr |= v << (memAddrThreshold << 2);
    change.addr = true;
    refresh()
}

function memAddrUp() {
    if (memAddrThreshold < 3) {
        memAddrThreshold++;
        memAddrMask <<= 4;
        change.addr = true;
        refresh();
    }
}

function memAddrDown() {
    if (memAddrThreshold > 0) {
        memAddrThreshold--;
        memAddrMask >>= 4;
        change.addr = true;
        refresh();
    }
}

function memAddrClear() {
    memAddr = 0;
    change.addr = true;
    refresh();
}

function memAddrEnter() {
    change.memory = true;
    refresh();
}

function memViewLeft() {
    if (memAddr < (1 << 16) - 8) {
        memAddr += 8
        change.addr = true;
        change.memory = true;
        refresh();
    }
}

function memViewRight() {
    if (memAddr > 0) {
        memAddr -= 8
        change.addr = true;
        change.memory = true;
        refresh();
    }
}

function stepBtn() {
    var temp = step();
    if (temp) {
        cur = temp;
        change.registry = true;
        change.memory = true;
        change.cur = true;
        change.out = true;
        refresh();
    }
}

function runBtn() {
    run();
    change.memory = true;
    change.out = true;
    change.registry = true;
    refresh();
}

function stopBtn() {
    halt();
    out += "<br>停止</br>";
    change.out = true;
    refresh();
}

function uploadBtn() {
    let inp = document.getElementById("file");
    let file, fr;
    if (!inp.files[0]) {
        alert("ファイルを入力してください");
    } else {
        file = inp.files[0];
        fr = new FileReader();
        fr.onload = receivedText;
        fr.readAsText(file);
    }
    function receivedText(e) {
        let lines = e.target.result;
        code = JSON.parse(lines);
    }
}

function downloadBtn() {
    var element = document.createElement('a');
    element.setAttribute('href', 'data:text/plain;charset=utf-8,' + encodeURIComponent(JSON.stringify(code)));
    element.setAttribute('download', "code.json");

    element.style.display = 'none';
    document.body.appendChild(element);

    element.click();

    document.body.removeChild(element);
}

function refresh() {
    if (change.addr) {
        let spans = $("table#memAddr td span");
        spans[3 - memAddrThreshold].style["background-color"] = "red";
        for (let i = 3, j = 0; i >= 0; i--, j++) {
            spans[i].innerHTML = lookup((memAddr & (0xf << (j << 2))) >> (j << 2));
            if (j != memAddrThreshold) {
                spans[3 - j].style["background-color"] = "";
            }
        }
    }
    if (change.memory) {
        let spanHeader = $("table#mem th span");
        let spanData = $("table#mem td span");
        for (let i = 7, j = 0; j < 8; i--, j++) {
            spanHeader[i].innerHTML = translate(memAddr + j);
            spanData[i].innerHTML = translate(getMemory(memAddr + j));
        }
    }
    if (change.registry) {
        let spans = $("table#reg td span");
        for (let i = 7, j = 0; j < 8; i--, j++) {
            spans[i].innerHTML = translate(getRegister(j));
        }
    }
    if (change.cur) {
        $("#cur").html(`${translate(getPC() - 1)}<br><br>${cur.kana}<br><br>${cur.text}<br><br>${cur.hex}<br><br>${cur.bin}`);
        $("#curasm").html(`${cur.asm}`);
    }
    if (change.out) {
        $("#out").html(out);
    }
    change.addr = false;
    change.memory = false;
    change.registry = false;
    change.cur = false;
    change.out = false;
}

function reload() {
    $("#cur").html("");
    $("#curasm").html("");
    out = "";
    change.memory = true;
    change.registry = true;
    change.out = true;
    load();
    unhalt();
    refresh();
}

$(document).ready(() => {
    load();
    unhalt();
    change.addr = true;
    change.memory = true;
    refresh();
});
