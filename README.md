# SyzSpec

## SyzSpec: Specification Generation for Linux Kernel Fuzzing via Under-Constrained Symbolic Execution

This paper received the **[Distinguished Paper Award](https://www.sigsac.org/ccs/CCS2025/awards/)** at CCS 2025.

[Paper PDF](https://www.cs.ucr.edu/~zhiyunq/pub/oakland23_syzdescribe.pdf) | [Slides PDF](CCS25.pdf)

```
@inproceedings{conf/ccs/SyzSpec25,
  author       = {Yu Hao and
                  Juefei Pu and
                  Xingyu Li and
                  Zhiyun Qian and
                  Ardalan Amiri Sani},
  title        = {SyzSpec: Specification Generation for Linux Kernel Fuzzing via Under-Constrained Symbolic Execution},
  year         = {2025},
}
```

## Build

SyzSpec is based on [KLEE](https://klee-se.org/), so please check the build instructions of KLEE.

## Usage

To generate specifications using SyzSpec, run the following command with the appropriate options:

```bash
path-of-build/bin/klee \
  --entry-point="entry_function" \
  --spec-arguments-index="the index of the argument for the first user input" \
  --spec-arguments-num="the number of arguments for the user inputs" \
  --spec-interface-name="name of syscall" \
  --spec-prefix="the prefix argument of the user inputs" \
  --spec-suffix="the suffix argument of the user inputs" \
  --spec-output="the name of output file" \
  ./built-in.bc
```

### Parameters
- `--entry-point`: The entry point function to analyze.
- `--spec-arguments-index`: The index of the argument for the first user input.
- `--spec-arguments-num`: The number of arguments for user inputs.
- `--spec-interface-name`: The name of the syscall interface.
- `--spec-prefix`: The prefix for user input arguments.
- `--spec-suffix`: The suffix for user input arguments.
- `--spec-output`: The name of the output file for the generated specification.

### Example

For generating a specification for the `ppp_ioctl` syscall:

```bash
/home/yhao016/git/23-proj/build/bin/klee \
  --entry-point=ppp_ioctl \
  --spec-arguments-index=1 \
  --spec-arguments-num=2 \
  --spec-interface-name=ioctl \
  --spec-prefix="fd fd_spec" \
  --spec-suffix="" \
  --spec-output="ioctl" \
  ./built-in.bc
```
