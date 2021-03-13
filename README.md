# LLVM-Data-Flow

#### How to run
```
cmake -DCMAKE_BUILD_TYPE=Release ../Transforms/LivenessAnalysis
```

```
make -j4
```

```
opt-11 -load ./libLLVMLivenessAnalysisPass.so -LivenessAnalysis ../../test_cases/1.ll
```