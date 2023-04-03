# Model-Based Testing (MBT) Library

This library provides a convenient way to perform model-based testing in your
Rust projects. It enables you to define a `Reactor` that executes actions,
registers invariants, and verifies the invariants are maintained throughout the
execution.

## Dependencies

This library requires the following additional Rust dependencies:

- [`gjson`](https://docs.rs/gjson): A library for parsing and querying JSON
  data.
- [`test_case`](https://docs.rs/test_case): A procedural macro for creating
  data-driven tests in Rust.

## Usage

To use this library, create a `Reactor` with an initial state function and
_register_ step functions, invariants, and invariant state functions as needed.
Then, use the `test()` method to execute a sequence of actions and check that
the invariants hold.

Here's an example of a simple banking system that demonstrates the usage of the
methods, including invariant functions:

```rs
use color_eyre::eyre::{eyre, Result};
use gjson::{self, Value as GJsonValue};
use serde_json::{json, Value as SerdeJsonValue};
use mbt::Reactor;

struct Bank {
    accounts: std::collections::HashMap<String, f64>,
}

fn init_bank(state: &GJsonValue) -> Result<Bank> {
    let mut bank = Bank {
        accounts: Default::default(),
    };
    state.get("accounts").each(|name, balance| {
        bank.accounts.insert(name.to_string(), balance.f64());
        true
    });
    Ok(bank)
}

fn deposit(bank: &mut Bank, state: &GJsonValue) -> Result<()> {
    let account = state.get("account").to_string();
    let amount = state.get("amount").f64();
    bank.accounts.entry(account).and_modify(|b| *b += amount);
    Ok(())
}

fn withdraw(bank: &mut Bank, state: &GJsonValue) -> Result<()> {
    let account = state.get("account").to_string();
    let amount = state.get("amount").f64();
    let balance = bank
        .accounts
        .get_mut(&account)
        .ok_or_else(|| eyre!("Account not found"))?;
    if *balance >= amount {
        *balance -= amount;
        Ok(())
    } else {
        Err(eyre!("Insufficient balance"))
    }
}

fn transfer(bank: &mut Bank, state: &GJsonValue) -> Result<()> {
    let src_account = state.get("src_account").to_string();
    let dst_account = state.get("dst_account").to_string();
    let amount = state.get("amount").f64();

    let src_balance = bank
        .accounts
        .get_mut(&src_account)
        .ok_or_else(|| eyre!("Source account not found"))?;

    if *src_balance >= amount {
        *src_balance -= amount;
        let dst_balance = bank
            .accounts
            .get_mut(&dst_account)
            .ok_or_else(|| eyre!("Destination account not found"))?;
        *dst_balance += amount;
        Ok(())
    } else {
        Err(eyre!("Insufficient balance in source account"))
    }
}

fn positive_balance(bank: &mut Bank, _state: &GJsonValue) -> Result<bool> {
    Ok(bank.accounts.values().all(|&balance| balance >= 0.0))
}

fn total_supply(
    bank: &mut Bank,
    _state: &GJsonValue,
) -> Result<SerdeJsonValue> {
    let total: f64 = bank.accounts.values().cloned().sum();
    Ok(json!({ "total_supply": total }))
}

#[test]
fn test_bank() -> Result<()> {
    let actions = vec![
        gjson::parse(
            r#"{ "tag": "init", "accounts": { "Alice": 1000.0, "Bob": 500.0 }}"#,
        ),
        gjson::parse(
            r#"{ "tag": "transfer", "src_account": "Alice", "dst_account": "Bob", "amount": 200.0 }"#,
        ),
        gjson::parse(
            r#"{ "tag": "transfer", "src_account": "Bob", "dst_account": "Alice", "amount": 150.0 }"#,
        ),
        gjson::parse(
            r#"{ "tag": "withdraw", "account": "Bob", "amount": 50.0 }"#,
        ),
        gjson::parse(
            r#"{ "tag": "deposit", "account": "Alice", "amount": 100.0 }"#,
        ),
    ];

    let mut reactor = Reactor::new("tag", init_bank);
    reactor.register("deposit", deposit);
    reactor.register("withdraw", withdraw);
    reactor.register("transfer", transfer);
    reactor.register_invariant(positive_balance);
    reactor.register_invariant_state(total_supply);
    reactor.test(&actions)?;

    Ok(())
}
```

This example test will fail, as _total supply_ is expected to remain constant.
But _deposit_ or _withdraw_ action violates that invariant.

## Project-specific usage

In a specific project, you may use this library with ITF trace as follows:

```rs
#[test_case::test_case("traces/example01.itf.json")]
#[test_case::test_case("traces/example02.itf.json")]
fn mbt_test(path: &str) -> Result<()> {
    let json_string = std::fs::read_to_string(path)?;
    let json_value = gjson::parse(&json_string);
    let mut reactor = Reactor::new(...);
    // ... code for step, invariant register
    reactor.test(&json_value.get("states").array())?;
    Ok(())
}
```

This example reads test cases from JSON files and executes the test using the
Reactor. Just replace the ... with the appropriate arguments and code for your
specific use case.
