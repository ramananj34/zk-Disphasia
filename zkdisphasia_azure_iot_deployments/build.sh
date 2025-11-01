#!/bin/bash
set -e

GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}=== Building ZK-DISPHASIA for IoT Devices ===${NC}\n"

# Targets
TARGETS=(
    "x86_64-unknown-linux-musl"
    "aarch64-unknown-linux-musl"
)

OUTPUT_DIR="./binaries"
mkdir -p "$OUTPUT_DIR"

# Build each target
for target in "${TARGETS[@]}"; do
    echo -e "${GREEN}Building $target...${NC}"
    
    # Build binaries
    cargo build --release --target "$target" --bin fixture_server
    cargo build --release --target "$target" --bin test_harness
    
    # Create output directory
    TARGET_DIR="$OUTPUT_DIR/$target"
    mkdir -p "$TARGET_DIR"
    
    # Copy binaries
    cp "target/$target/release/fixture_server" "$TARGET_DIR/"
    cp "target/$target/release/test_harness" "$TARGET_DIR/"
    
    # Strip debug symbols
    strip "$TARGET_DIR/fixture_server"
    strip "$TARGET_DIR/test_harness"
    
    # Show sizes
    echo -e "${BLUE}Binary sizes:${NC}"
    ls -lh "$TARGET_DIR/" | grep -E "(fixture_server|test_harness)" | awk '{print "  " $9 ": " $5}'
    
    # Verify static linking
    echo -e "${YELLOW}Checking dependencies:${NC}"
    ldd "$TARGET_DIR/test_harness" 2>&1 | head -2 || echo "  ✓ Statically linked"
    
    echo -e "${GREEN}✓ Completed $target${NC}\n"
done

# Copy trusted setup if exists
if [ -d "trusted_setup" ]; then
    echo -e "${GREEN}Copying trusted setup files...${NC}"
    for target in "${TARGETS[@]}"; do
        cp -r trusted_setup "$OUTPUT_DIR/$target/"
    done
fi

# Generate checksums
echo -e "${GREEN}Generating checksums...${NC}"
cd "$OUTPUT_DIR"
find . -type f \( -name "fixture_server" -o -name "test_harness" \) -exec sha256sum {} \; > checksums.txt
cd ..

# Create deployment packages
echo -e "\n${GREEN}Creating deployment packages...${NC}"
cd "$OUTPUT_DIR"
for target in "${TARGETS[@]}"; do
    tar czf "zk-disphasia-${target}.tar.gz" "${target}/"
    SIZE=$(du -h "zk-disphasia-${target}.tar.gz" | cut -f1)
    echo "  ✓ zk-disphasia-${target}.tar.gz ($SIZE)"
done
cd ..

echo -e "\n${GREEN}=== Build Complete ===${NC}"
echo -e "${BLUE}Binaries: $OUTPUT_DIR${NC}"
echo -e "${BLUE}Packages:${NC}"
ls -lh "$OUTPUT_DIR"/*.tar.gz | awk '{print "  " $9 " (" $5 ")"}'

# Copy to Windows (optional)
WIN_OUTPUT="/mnt/c/Users/$USER/Desktop/zk-disphasia-binaries"
echo -e "\n${YELLOW}Copy to Windows Desktop? (y/n)${NC}"
read -r response
if [[ "$response" =~ ^[Yy]$ ]]; then
    mkdir -p "$WIN_OUTPUT"
    cp "$OUTPUT_DIR"/*.tar.gz "$WIN_OUTPUT/"
    echo -e "${GREEN}✓ Copied to: C:\\Users\\$USER\\Desktop\\zk-disphasia-binaries${NC}"
fi