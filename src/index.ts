import CodeMirror from "codemirror";
import "codemirror/lib/codemirror.css";
import "codemirror/mode/clike/clike.js";
import "./index.css";

class IDE {
    panels: {
        benchmarks: HTMLDivElement;
        editor: HTMLDivElement;
        output: HTMLDivElement;
    };
    cm: CodeMirror.Editor;
    paths: any[] | null;

    constructor() {
        this.panels = {
            benchmarks: document.querySelector("#panel-benchmarks"),
            editor: document.querySelector("#panel-editor"),
            output: document.querySelector("#panel-output"),
        };

        this.cm = CodeMirror(this.panels.editor, {
            lineNumbers: true,
            //matchBrackets: true,
            mode: "text/x-csrc",
            indentUnit: 4,
            value: `#include "common.h"

int array_max_bug(int arr[], int size) {
    requires(size > 0);
    ensures(
        exists(k, range(0, size), ret == arr[k])
        && forall(k, range(0, size), arr[k] <= ret)
    );
    int max = arr[0];
    for (int i = 0; i != size; i++) {
        if (arr[i] <= max) {
            max = arr[i];
        }
        assert(exists(k, range(0, i + 1), max == arr[k]) && forall(k, range(0, i + 1), arr[k] <= max));
    }
    return max;
}`,
        });

        this.panels.output
            .querySelector("button")
            .addEventListener("click", () => this.runVerifier());
    }

    async open(uri: string) {
        var text = await (await fetch(uri)).text(),
            doc = new CodeMirror.Doc(text, "text/x-csrc");
        this.cm.swapDoc(doc);
    }

    async runVerifier() {
        const out = await fetch("/verify", {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
            },
            body: JSON.stringify({
                action: "verify",
                code: this.cm.getDoc().getValue(),
            }),
        });
        const js = await out.json();
        if (js.ok) {
            const output = this.panels.output.querySelector("#output");
            const fail_panel = this.panels.output.querySelector("#v-fail");
            if (js.verified) {
                output.textContent = "OK";
                fail_panel.innerHTML = "";
                this.paths = null;
            } else {
                output.innerHTML = '<p>FAIL</p><button id="clear_paths">clear paths</button>';
                document.getElementById("clear_paths").onclick = () => this.clear_all_marks();
                let ht = "";
                this.paths = js.body;
                for (const p of js.body) {
                    ht += `
                    <div id="path_${p.index}">
                    <h2>path ${p.index}</h2>
                    <p>${p.prop}</p>
                    <button id="show_path_${p.index}">show path</button>
                    <h4>reachability condition</h4>
                    <p>${p.reachability}</p>`;
                    ht += "<h4>transformation</h4>";
                    for (const t of p.transformation) {
                        ht += `<p>${t}</p>`;
                    }
                    ht += "<h4>model</h4>";
                    for (const t of p.model) {
                        ht += `<p>${t}</p>`;
                    }
                    ht += "</div>";
                }
                fail_panel.innerHTML = ht;
                for (const p of js.body) {
                    document.getElementById(`show_path_${p.index}`).onclick =
                        () => this.show_path(p.index);
                }
            }
        }
    }

    clear_all_marks() {
        for (const text of this.cm.getAllMarks()) {
            text.clear();
        }
    }

    show_path(index: number) {
        this.clear_all_marks();
        for (const range of this.paths[index].ranges) {
            this.cm.markText(
                { line: range.start_line - 1, ch: range.start_column - 1 },
                { line: range.end_line - 1, ch: range.end_column - 1 },
                {
                    className: "highlight-code",
                },
            );
        }
    }

    /* async listBenchmarks() {
        var ul = this.panels.benchmarks.querySelector("#benchmarks"),
            items = await (await fetch("/benchmarks")).json();
        for (let item of items) {
            var li = document.createElement("li");
            li.textContent = item;
            ul.append(li);
        }
    } */
}

function main() {
    var ide = new IDE();
    // ide.listBenchmarks();
    ide.cm.focus();

    // ide.open('/');

    // Useful for debugging in dev console
    Object.assign(window, { ide });
}

document.addEventListener("DOMContentLoaded", main);
