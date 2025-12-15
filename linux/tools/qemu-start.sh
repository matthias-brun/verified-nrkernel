

# sudo apt-get install libvirt-clients libvirt-daemon-system \
#   bridge-utils virtinst libvirt-daemon guestfs-tools libguestfs-tools
# sudo apt install qemu-system-x86_64

VM_DIR=vm

KERNEL_VERSION=$(uname -r)

INITRD="/boot/initrd.img-$KERNEL_VERSION"
KERNEL="/boot/vmlinuz-$KERNEL_VERSION"


CMDLINE="BOOT_IMAGE=/boot/vmlinuz-${KERNEL_VERSION} root=LABEL=cloudimg-rootfs rw console=ttyS0 nopti ibt=off no5lvl"
DISK=$VM_DIR/noble-server-cloudimg-amd64.img
DISK=$VM_DIR/ubuntu-cloud.qcow2

LOCAL_PATH=$(pwd)

echo "Copying data into the disk..."
echo " -- module..."
virt-copy-in -a  $DISK module /root
echo " -- user..."
virt-copy-in -a  $DISK user /root
echo " -- tools..."
virt-copy-in -a  $DISK tools /root
virt-copy-in -a  $DISK Makefile /root
echo "done."

qemu-system-x86_64  \
  -machine accel=kvm,type=q35 \
  -cpu Cascadelake-Server \
  -smp 4 \
  -m 8G \
  -kernel $KERNEL \
  -initrd $INITRD \
  -append "$CMDLINE" \
  -nographic \
  -drive if=virtio,format=qcow2,file=$DISK

# -nographic \

  # -virtfs local,path=$LOCAL_PATH,mount_tag=host0,security_model=passthrough,id=host0

# ,script=no,downscript=no

 # -drive file=user-data.img,format=raw \


  # -device virtio-net-pci,netdev=net0 \
  # -netdev user,id=net0,hostfwd=tcp::2222-:22 \

 # -netdev tap,id=mynet0,ifname=tap0 \
 # -device virtio-net-pci,netdev=mynet0,mac=52:55:00:d1:55:01 \

# mount -t 9p -o trans=virtio [mount tag] [mount point] -oversion=9p2000.L
# mount -t 9p -o trans=virtio host0 /mnt/shared -oversion=9p2000.L


# /etc/systemd/system/network-online.target.wants/systemd-networkd-wait-online.service