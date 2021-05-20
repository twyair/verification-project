hljs.highlightAll();

var selected_path = null;

function highlight_path(path_classes) {
    for (const r of path_classes) {
        const elem = document.getElementsByClassName(r);
        for (const e of elem) {
            e.classList.add("highlight");
        }
    }
}

function unhighlight_path(path_classes) {
    for (const r of path_classes) {
        const elem = document.getElementsByClassName(r);
        for (const e of elem) {
            e.classList.remove("highlight");
        }
    }
}

function select_path() {
    if (selected_path !== null) {
        const path = document.getElementById("path" + selected_path);
        unhighlight_path(JSON.parse(path.dataset.classes));
        path.setAttribute("hidden", "");
    }
    const index = document.getElementById("select-path").value;
    selected_path = index;
    const path_element = document.getElementById("path" + index);
    path_element.removeAttribute("hidden");
    highlight_path(JSON.parse(path_element.dataset.classes));
}

const code_block = document.getElementById("code");
code_block.scrollTo({top: code_block.scrollHeight * parseInt(code_block.dataset.curr_line) / parseInt(code_block.dataset.total_lines) });