// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{ErrorKind, Result};
use ::std::env;
use ::std::io::{Read, Write};
use ::std::process::Command;
use ::std::process::Stdio;

pub fn format(input: &str) -> Result<String> {
    let rustfmt_exe = env::var("RUSTFMT").unwrap_or("rustfmt".to_string());
    let rustfmt = Command::new(&rustfmt_exe)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;

    let mut stdin = rustfmt.stdin.ok_or(ErrorKind::InternalError {
        detail: "no stdin bound for rustfmt child process".to_string(),
    })?;
    stdin.write_all(input.as_bytes())?;

    let mut stdout = rustfmt.stdout.ok_or(ErrorKind::InternalError {
        detail: "no stdout bound for rustfmt child process".to_string(),
    })?;
    let mut out = String::new();
    stdout.read_to_string(&mut out)?;

    return Ok(out);
}
