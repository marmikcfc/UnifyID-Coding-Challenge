from gan import run_gan
from rsa import generate_key_pair
import sys


if __name__ == "__main__":
	assert len(sys.argv) == 2, "Please use rsa or image to run either one of those"
	acceptable_flags = ["rsa", "image"]
	flag = str(sys.argv[1])
	assert flag in acceptable_flags, "Incorrect command line input. Please use rsa or image "
	if flag == "rsa":
		generate_key_pair()
		print("rsa key pair generated")
	elif flag == "image":
		run_gan()