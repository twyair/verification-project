hljs.highlightAll();

var selected_invariant = null;

const code_block = document.getElementById("code");
code_block.scrollTo({top: code_block.scrollHeight * parseInt(code_block.dataset.curr_line) / parseInt(code_block.dataset.total_lines) });

function highlight_cutpoint(cls) {
    const elem = document.getElementsByClassName(cls);
    for (const e of elem) {
        e.classList.add("highlight");
    }
}

function unhighlight_cutpoint(cls) {
    const elem = document.getElementsByClassName(cls);
    for (const e of elem) {
        e.classList.remove("highlight");
    }
}

function select_invariant() {
    if (selected_invariant !== null) {
        const div = document.getElementById("inv" + selected_path);
        unhighlight_cutpoint([div.dataset.range]);
        div.setAttribute("hidden", "");
    }
    const index = document.getElementById("select-invariant").value;
    selected_invariant = index;
    const div = document.getElementById("inv" + index);
    highlight_cutpoint(div.dataset.range);
    div.removeAttribute("hidden");
}