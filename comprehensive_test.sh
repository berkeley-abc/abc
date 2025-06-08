#!/bin/bash

# Comprehensive test for pbo_ prefix implementation across different gate types
echo "=== Comprehensive pbo_ prefix test ==="
echo

# Test the complex circuit
echo "Testing complex circuit with multiple gate types..."

cat > complex_test_commands.abc << 'EOF'
# Read complex test circuit
read benchmarks/complex_test.blif
echo "Loaded complex test circuit"

# Show circuit statistics
print_stats

# Generate faults
fault_gen -c
echo "Generated fault list"

# Show fault list
print_faults

# Run fault simulation with pbo_ prefix gates
fault_sim -c
echo "Inserted fault simulation gates with pbo_ prefix"

# Write output
write_verilog benchmarks/complex_test_with_pbo.v
echo "Written complex circuit with pbo_ gates"

quit
EOF

./abc -f complex_test_commands.abc

echo
echo "=== Results for complex circuit ==="
if [ -f "benchmarks/complex_test_with_pbo.v" ]; then
    echo "Number of pbo_ occurrences:"
    grep -c "pbo_" benchmarks/complex_test_with_pbo.v
    
    echo
    echo "Types of pbo_ gates found:"
    grep "pbo_" benchmarks/complex_test_with_pbo.v | grep -o "pbo_[a-z]*" | sort | uniq
    
    echo
    echo "Sample pbo_ gate implementations:"
    grep -n "assign.*pbo_" benchmarks/complex_test_with_pbo.v | head -10
else
    echo "Error: Complex test output not generated"
fi

# Clean up
rm -f complex_test_commands.abc

echo
echo "=== Comprehensive test finished ==="
