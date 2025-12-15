#
#  install `guestfs-tools cloud-image-utils`
#
# If things fail, it can be that there is no permissions in accessing the kernel
# change the permissions of vmlinuz in /boot

set -x

# the image name
IMAGE_NAME=ubuntu-cloud.qcow2

# the output directory
OUTPUT_DIRECTORY=vm

# the url to download from
DL_IMAGE_NAME=noble-server-cloudimg-amd64.img
IMAGE_URL=https://cloud-images.ubuntu.com/noble/current/$DL_IMAGE_NAME

mkdir -p $OUTPUT_DIRECTORY

if [ ! -f $OUTPUT_DIRECTORY/$DL_IMAGE_NAME ]; then
    echo "Downloading $DL_IMAGE_NAME from $IMAGE_URL"
    wget -O $OUTPUT_DIRECTORY/$DL_IMAGE_NAME $IMAGE_URL
else
    echo "$OUTPUT_DIRECTORY/$DL_IMAGE_NAME already exists"
fi

rm -rf $OUTPUT_DIRECTORY/$IMAGE_NAME

# increase the module size
qemu-img create -f qcow2 -o preallocation=metadata $OUTPUT_DIRECTORY/$IMAGE_NAME 16G

# list the partitions
virt-filesystems --partitions --long -a $OUTPUT_DIRECTORY/$DL_IMAGE_NAME
virt-filesystems --long -h --all -a $OUTPUT_DIRECTORY/$DL_IMAGE_NAME

# resize the image
virt-resize --expand /dev/sda1 $OUTPUT_DIRECTORY/$DL_IMAGE_NAME $OUTPUT_DIRECTORY/$IMAGE_NAME

# list the file systems
echo "partitions: "
virt-filesystems --partitions --long -a $OUTPUT_DIRECTORY/$IMAGE_NAME
virt-filesystems --partitions --long -a $OUTPUT_DIRECTORY/$DL_IMAGE_NAME
echo "filesystems: "
virt-filesystems --long -h --all -a $OUTPUT_DIRECTORY/$IMAGE_NAME
virt-filesystems --long -h --all -a $OUTPUT_DIRECTORY/$DL_IMAGE_NAME

# list the boot folder
# virt-ls -a $OUTPUT_DIRECTORY/$IMAGE_NAME /etc/netplan/

# copy out the kernel and initrd
virt-copy-out -a $OUTPUT_DIRECTORY/$IMAGE_NAME /boot/initrd.img-6.8.0-79-generic $OUTPUT_DIRECTORY
virt-copy-out -a $OUTPUT_DIRECTORY/$IMAGE_NAME /boot/vmlinuz-6.8.0-79-generic $OUTPUT_DIRECTORY

# virt-copy-out -a $OUTPUT_DIRECTORY/$IMAGE_NAME /etc/netplan/50-cloud-init.yaml $OUTPUT_DIRECTORY

# create the shared folder
virt-customize -a $OUTPUT_DIRECTORY/$IMAGE_NAME  --mkdir /mnt/shared
virt-copy-out -a $OUTPUT_DIRECTORY/$IMAGE_NAME /etc/fstab $OUTPUT_DIRECTORY
# echo "" >> $OUTPUT_DIRECTORY/fstab
# echo "# mount the plan9 fs" >> $OUTPUT_DIRECTORY/fstab
# echo "/mnt/shared   /mnt/shared   9p  trans=virtio,rw,_netdev 0   0" >> $OUTPUT_DIRECTORY/fstab
# virt-copy-in -a  $OUTPUT_DIRECTORY/$IMAGE_NAME $OUTPUT_DIRECTORY/fstab /etc/fstab

# set the default passwords
virt-customize -a $OUTPUT_DIRECTORY/$IMAGE_NAME  --root-password password:pw
virt-customize -a $OUTPUT_DIRECTORY/$IMAGE_NAME  --password ubuntu:password:ubuntu


# disable service
virt-customize -a $OUTPUT_DIRECTORY/$IMAGE_NAME  --delete /etc/systemd/system/network-online.target.wants/systemd-networkd-wait-online.service


# virt-customize -a $OUTPUT_DIRECTORY/$IMAGE_NAME  --network --install gdb

cat >$OUTPUT_DIRECTORY/user-data <<EOF
#cloud-config
password: ubuntu
chpasswd: { expire: False }
ssh_pwauth: True
EOF