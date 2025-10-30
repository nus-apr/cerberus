#!/usr/bin/env bash
# setup-podman.sh
# Configure Podman to work with Cerberus framework

set -e

echo "=== Cerberus Podman Setup ==="
echo

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get user ID for socket path
USER_ID=$(id -u)
PODMAN_SOCKET_PATH="/run/user/${USER_ID}/podman/podman.sock"

# Step 1: Enable and start Podman socket
echo -e "${YELLOW}[1/2]${NC} Enabling Podman socket service..."
if systemctl --user enable --now podman.socket 2>/dev/null; then
    echo -e "${GREEN}✓${NC} Podman socket enabled and started"
else
    echo -e "${RED}✗${NC} Failed to enable Podman socket"
    exit 1
fi

# Step 2: Verify socket exists
echo -e "${YELLOW}[2/2]${NC} Verifying Podman socket..."
if [ -S "$PODMAN_SOCKET_PATH" ]; then
    echo -e "${GREEN}✓${NC} Podman socket found at: $PODMAN_SOCKET_PATH"
else
    echo -e "${RED}✗${NC} Podman socket not found at: $PODMAN_SOCKET_PATH"
    echo "    Try running: systemctl --user status podman.socket"
    exit 1
fi

DOCKER_HOST_EXPORT="export DOCKER_HOST=unix://${PODMAN_SOCKET_PATH}"

echo
echo "=== Setup Complete ==="
echo
echo "To use Cerberus with Podman in the current session, run:"
echo -e "${GREEN}  $DOCKER_HOST_EXPORT${NC}"
echo
echo "Example Cerberus command:"
echo -e "${GREEN}  cerberus -task repair --bug-index=1 --benchmark=manybugs --tool=esbmcai${NC}"
echo
echo -e "Alternatively add it to your rc file to automatically use it."
echo

# Export for current session
eval "$DOCKER_HOST_EXPORT"
echo -e "${GREEN}✓${NC} DOCKER_HOST exported for current session"
