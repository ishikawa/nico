# nico

![Github Action workflow](https://github.com/ishikawa/nico/actions/workflows/build.yml/badge.svg)

Just for `fun` 🙂

## ~~Install~~

Not recommended for now. It's under heavily development.

## Build the compiler

The compiler is written in [Rust](https://www.rust-lang.org/). You can build it with `cargo`.

```bash
$ cargo build
```

## Compile

The directory [`samples`](https://github.com/ishikawa/nico/tree/main/samples) contains some example programs. Let's compile a [Fizz buzz](https://en.wikipedia.org/wiki/Fizz_buzz) because we all love it.

```ruby
fun _fizzbuzz(i, n)
    if i <= n
        case i
        when x if x % 15 == 0
            println_str("Fizz Buzz")
        when x if x % 3 == 0
            println_str("Fizz")
        when x if x % 5 == 0
            println_str("Buzz")
        else
            println_i32(i)
        end
        _fizzbuzz(i + 1, n)
    end
end

export fun fizzbuzz(n)
    _fizzbuzz(1, n)
end

fizzbuzz(15)
```

The compiler reads from a file (or standard input) and output [WASM Text Format](https://webassembly.github.io/spec/core/text/index.html) to standard output.

```bash
./target/debug/nico samples/fizzbuzz.nico > fizzbuzz.wat
```

## Run

`npm run nico` reads a `.wat` file and execute `main` function which is produced by the compiler.

```bash
$ npm run nico ./fizzbuzz.wat

> nico@1.0.0 nico /Users/ishikawasonkyou/Developer/Workspace/nico
> ts-node ./runner/cli.ts "./fizzbuzz.wat"

1
2
Fizz
4
Buzz
Fizz
7
8
Fizz
Buzz
11
Fizz
13
14
Fizz Buzz
```

## FAQ

### Why the name "nico"?

Japanese people express "nicely smiling" as "NICO-NICO". I think programming should be fun and makes people smile. So I picked the keyword `fun` for *function*s and named my programming language `nico`.
