use std::io::Read;

use starknet_in_rust::services::api::contract_classes::deprecated_contract_class::ContractClass;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    if std::env::args().count() != 1 {
        println!("parse_class_definition -- reads from stdin");
        println!(
            "the input read from stdin is expected to be a class definition, which is a json blob."
        );
        std::process::exit(1);
    }
    let mut definition = String::new();
    std::io::stdin().read_to_string(&mut definition).unwrap();
    let _contract_class: ContractClass = definition.as_str().try_into()?;

    Ok(())
}
