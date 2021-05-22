hljs.highlightAll();

var selected_invariant = null;

const code_block = document.getElementById("code");
code_block.scrollTo({top: code_block.scrollHeight * parseInt(code_block.dataset.curr_line) / parseInt(code_block.dataset.total_lines) });

function select_invariant() {
    if (selected_invariant !== null) {
        document.getElementById("inv" + selected_path).setAttribute("hidden", "");
    }
    const index = document.getElementById("select-invariant").value;
    selected_invariant = index;
    document.getElementById("inv" + index).removeAttribute("hidden");
}