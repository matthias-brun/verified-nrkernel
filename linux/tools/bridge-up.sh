
MY_ETH=ens1f0np0

# Create a bridge
brctl addbr br0

# Clear IP of eth0
ip addr flush dev eth0

# Add eth0 to bridge
brctl addif br0 eth0

#Create tap interface
tunctl -t tap0 -u `whoami`

# Add tap0 to bridge
brctl addif br0 tap0


# Make sure everything is up
ifconfig eth0 up
ifconfig tap0 up
ifconfig br0 up

# Check if properly bridged
brctl show

# Assign ip to br0
dhclient -v br0