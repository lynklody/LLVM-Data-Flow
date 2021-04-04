# LLVM-Data-Flow

#### How to run

Run the following commands at dir /Pass/build
```
cmake -DCMAKE_BUILD_TYPE=Release ../Transforms/LivenessAnalysis
```

```
make -j4
```

```
opt-11 -load ./libLLVMLivenessAnalysisPass.so -LivenessAnalysis ../../test_cases/1.ll
```
