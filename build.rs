fn main() {
    println!("cargo:rerun-if-changed=src/jqish.lalrpop");
    lalrpop::process_root().unwrap();
}
