# SyzSpec

## SyzSpec: Specification Generation for Linux Kernel Fuzzing via Under-Constrained Symbolic Execution

[PDF](https://www.cs.ucr.edu/~zhiyunq/pub/oakland23_syzdescribe.pdf)
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

SyzSpec is based on KLEE, so please check the build instructions of KLEE.

## Usage

path-of-build/bin/klee --entry-point="entry_function" --spec-arguments-index="the index of the arguement for the first user input" --spec-arguments-num="the number of arguments for the user inputs" --spec-
interface-name="name of syscall" --spec-prefix="the prefix arguement of the user inputs" --spec-suffix="the suffix argument of the user inputs" --spec-output="the name of output file" ./built-in.bc

e.g., /home/yhao016/git/23-proj/build/bin/klee --entry-point=ppp_ioctl --spec-arguments-index=1 --spec-arguments-num=2 --spec-
interface-name=ioctl --spec-prefix="fd fd_spec" --spec-suffix="" --spec-output="ioctl" ./built-in.bc
