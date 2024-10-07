# Memory Allocator

## Explanation
The CS:APP Malloc Lab focuses on implementing a dynamic memory allocator in C. This project optimizes memory allocation techniques to achieve high utilization and throughput. The goal is to create an efficient allocator that can handle various allocation requests, with specific attention to performance metrics like operations per second and memory utilization.

The project implements a dynamic memory allocator in C, optimizing for:
- Explicit Free Lists: Enhancing memory management efficiency.
- Footer Removal: Streamlining allocated blocks.
- Best-fit and First-fit Merging: Balancing allocation speed and memory use.

The final implementation achieves 1.1M operations per second and 74% memory utilization.

## Execution Instructions
To successfully build and test the allocator, follow these steps:

1. **Build the Driver**  
   Run the following command in the terminal:  
   ```
   make
   ```

3. **Run Tests**  
   Execute the driver with a small test trace:  
   ```
   ./mdriver -V -f traces/malloc.rep
   ```  
   To see a list of available driver flags, use:  
   ```
   ./mdriver -h
   ```  
   The ```-V``` option provides helpful tracing information.

5. **Debugging**  
   For testing with debugging enabled, run:  
   ```
   ./mdriver-dbg
   ```

7. **Testing 64-bit Address Handling**  
   To verify the code's handling of 64-bit addresses:  
   ```
   ./mdriver-emulate
   ```  
   Ensure that utilization numbers match those obtained from the regular driver, noting that timing data will be zero.

9. **MemorySanitizer Check**  
   To check for uninitialized memory usage, execute:  
   ```./mdriver-uninit```

## Structure
- ```mm.c```: Implicit-list allocator (recommended starting point).
- ```mm-naive.c```: Fast but memory-inefficient allocator.
