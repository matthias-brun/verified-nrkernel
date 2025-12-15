# MIT License
#
# Copyright (c) 2025 Paper #409 Authors, ASPLOS'26.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import json
import sys
import matplotlib.pyplot as plt
import numpy as np
import os


def main():
    # load the json file passed as argument
    if len(sys.argv) != 2:
        print("Usage: python plot.py <json_file>")
        sys.exit(1)
    json_file = sys.argv[1]
    if not os.path.isfile(json_file):
        print(f"File {json_file} does not exist.")
        sys.exit(1)
    with open(json_file, 'r') as f:
        data = json.load(f)
    print(str(data["times-ms"]["num-threads"]) + " threads")
    print(str(data["times-ms"]["total"] / 1000) + " seconds (real time)")
    print("for an estimated " + str(data["times-ms"]["estimated-cpu-time"] / 1000) + " seconds of cpu time")
    mm = [m["function-breakdown"] for m in data["times-ms"]["smt"]["smt-run-module-times"]]
    mm = [item['time'] / 1000 for sublist in mm for item in sublist if item['time'] > 0]
    print(mm)
    # plot a ccdf of mm
    plt.figure()
    sorted_mm = np.sort(mm)
    print(len(sorted_mm))
    ccdf = np.arange(1, len(sorted_mm) + 1)
    p = plt.plot(ccdf, sorted_mm, label="CDF")
    # plt.gca().set_position([0.2, 0.2, 0.6, 0.6])

    plt.gcf().set_size_inches(7.8, 2.2)  # Set the figure size to make the plot smaller
    plt.yscale('log')
    plt.ylim(0.0009, 80)
    plt.yticks(ticks=[0.001, 0.01, 0.1, 1, 10, 100], labels=["0.001", "0.01", "0.1", "1", "10", "100"])
    # plt.xticks(ticks=[2* t / 10 for t in range(0, 6)], labels=[f"{t * 20}%" for t in range(0, 6)])
    plt.xlim(0, max(ccdf))
    # increase the font sizes
    plt.xticks(fontsize=14)
    plt.yticks(fontsize=14)
    # plt.xlabel('Percentage of verified functions', fontsize=14)
    plt.ylabel('Verif. time [sec]', fontsize=14)
    # plt.title('CDF of function verification times', fontsize=14)
    # plt.legend(fontsize=14)
    # plt.legend()
    plt.grid()
    plt.savefig(json_file + ".png")

if __name__ == "__main__":
    main()
