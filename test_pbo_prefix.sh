#!/bin/bash

# Test script for pbo_ prefix verification in SAT-based ATPG system
echo "=== Testing pbo_ prefix implementation ==="
echo

# Start ABC and run test sequence
echo "Starting ABC and testing pbo_ prefix functionality..."
echo

# Create input commands for ABC
cat > test_commands.abc << 'ABCEOF'
# Read test circuit
read benchmarks/test.blif
echo "Loaded test circuit"

# Generate faults using checkpoint method 
fault_gen -c
echo "Generated fault list"

# Show fault list (optional for debugging)
print_faults

# Run fault simulation with pbo_ prefix gates
fault_sim -c
echo "Inserted fault simulation gates with pbo_ prefix"

# Write output to see the modified circuit
write_verilog benchmarks/test_with_pbo.v
echo "Written circuit with pbo_ gates to test_with_pbo.v"

# Exit ABC
quit
ABCEOF

# Run ABC with the test commands
echo "Running ABC with test commands..."
./abc -f test_commands.abc

echo
echo "=== Test completed ==="
echo "Checking output files for pbo_ prefix verification..."

# Check if the output file contains pbo_ prefixed gates
if [ -f "benchmarks/test_with_pbo.v" ]; then
    echo
    echo "=== Checking for pbo_ prefixed gates in output ==="
    echo "Searching for 'pbo_' in generated Verilog file:"
    grep -n "pbo_" benchmarks/test_with_pbo.v || echo "No pbo_ prefixes found in Verilog output"
    
    echo
    echo "=== First 50 lines of generated Verilog file ==="
    head -50 benchmarks/test_with_pbo.v
else
    echo "Error: Output file not generated"
fi

# Clean up
rm -f test_commands.abc

echo
echo "=== Test script finished ==="
