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
    invariants: any[] | null;
    selected_path: any | null;

    constructor() {
        this.panels = {
            benchmarks: document.querySelector("#panel-benchmarks"),
            editor: document.querySelector("#panel-editor"),
            output: document.querySelector("#panel-output"),
        };

        this.cm = CodeMirror(this.panels.editor, {
            lineNumbers: true,
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
        this.cm.on("change", (instance, changeObj) => this.clear_all_marks());

        this.panels.output
            .querySelector("#verify")
            .addEventListener("click", () => this.runVerifier());

        this.panels.output
            .querySelector("#horn")
            .addEventListener("click", () => this.run_horn());

        this.invariants = null;
        this.paths = null;
        this.selected_path = null;
    }

    async open(uri: string) {
        var text = await (await fetch(uri)).text(),
            doc = new CodeMirror.Doc(text, "text/x-csrc");
        this.cm.swapDoc(doc);
    }

    async run(uri: string): Promise<any> {
        const out = await fetch(uri, {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
            },
            body: JSON.stringify({
                code: this.cm.getDoc().getValue(),
            }),
        });
        return await out.json();
    }

    async run_horn() {
        this.clear_all_marks();
        const js = await this.run("/horn");
        const output = this.panels.output.querySelector("#output");
        if (js.ok) {
            this.panels.output.querySelector("#v-fail").innerHTML = "";
            if (js.verified) {
                let ht = "<p>OK</p><button id='clear_locations'>clear</button>";
                this.invariants = js.invariants;
                for (const inv of this.invariants) {
                    ht += `
                        <div id=inv_${inv.index}>
                        <h2>invariant ${inv.name}</h2>
                        <button id="locate_inv_${inv.index}">locate</button>
                        <p>${inv.expr}</p>
                        </div>
                    `;
                }
                output.innerHTML = ht;
                for (const inv of this.invariants) {
                    document.getElementById(`locate_inv_${inv.index}`).onclick =
                        () => this.locate_inv(inv.index);
                }
                document.getElementById("clear_locations").onclick = () => this.clear_all_marks();
            } else {
                output.innerHTML = "<p>FAIL</p>";
                this.invariants = null;
            }
        } else {
            output.innerHTML = `<h2>ERROR</h2><p>${js.err}</p>`;
        }
    }

    async runVerifier() {
        this.clear_all_marks();
        const js = await this.run("/verify");
        const output = this.panels.output.querySelector("#output");
        const fail_panel = this.panels.output.querySelector("#v-fail");
        if (js.ok) {
            if (js.verified) {
                output.textContent = "OK";
                fail_panel.innerHTML = "";
                this.paths = null;
            } else {
                output.innerHTML =
                    '<p>FAIL</p><button id="clear_paths">clear paths</button>';
                document.getElementById("clear_paths").onclick = () =>
                    this.clear_all_marks();
                let ht = "";
                ht += "<select id='select_path'><option disabled selected value> -- select an option -- </option>"
                for (let i = 0; i < js.body.length; i++) {
                    ht += `<option value="path_${i}">path ${i}</option>`;
                }
                ht += "</select>"
                this.paths = js.body;
                for (const p of js.body) {
                    ht += `
                    <div id="path_${p.index}" hidden>
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
                document.getElementById("select_path").onchange = () => this.select_path();
            }
        } else {
            output.innerHTML = `<h2>ERROR</h2><p>${js.err}</p>`;
            fail_panel.innerHTML = "";
        }
    }

    select_path() {
        const path_id = (<HTMLSelectElement>document.getElementById("select_path")).value;
        if (this.selected_path !== null) {
            document.getElementById(this.selected_path).setAttribute("hidden", "");
        }
        document.getElementById(path_id).removeAttribute("hidden");
        this.selected_path = path_id;
    }

    clear_all_marks() {
        for (const text of this.cm.getAllMarks()) {
            text.clear();
        }
    }

    highlight_range(range: {
        start_line: number;
        start_column: number;
        end_line: number;
        end_column: number;
    }) {
        this.cm.markText(
            { line: range.start_line - 1, ch: range.start_column - 1 },
            { line: range.end_line - 1, ch: range.end_column - 1 },
            {
                className: "highlight-code",
            },
        );
    }

    show_path(index: number) {
        this.clear_all_marks();
        for (const range of this.paths[index].ranges) {
            this.highlight_range(range);
        }
    }

    locate_inv(index: number) {
        this.clear_all_marks();
        this.highlight_range(this.invariants[index].range);
    }

    async listBenchmarks() {
        var select = document.querySelector("#benchmarks"),
            items = await (await fetch("/benchmarks")).json();
        for (let item of items.sort()) {
            const option = document.createElement("option");
            option.textContent = item;
            option.value = item;
            select.append(option);
        }
        select.addEventListener("change", () => {
            const val = (<HTMLSelectElement>document.querySelector("#benchmarks")).value;
            this.get_source_code(val);
        });
    }

    async get_source_code(filename: string) {
        const code = await (await fetch(`/get_source?filename=${filename}`)).json();
        this.cm.setValue(code.code);
    }
}

function main() {
    var ide = new IDE();
    ide.listBenchmarks();
    ide.cm.focus();

    // ide.open('/');

    // Useful for debugging in dev console
    Object.assign(window, { ide });
}

document.addEventListener("DOMContentLoaded", main);
