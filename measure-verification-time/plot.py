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
    mm = [item['time'] for sublist in mm for item in sublist if item['time'] > 0]
    print(mm)
    # plot a ccdf of mm
    plt.figure()
    sorted_mm = np.sort(mm)
    ccdf = 1.0 - np.arange(1, len(sorted_mm) + 1) / len(sorted_mm)
    plt.plot(ccdf, sorted_mm, label="CCDF")
    plt.gcf().set_size_inches(3, 2)  # Set the figure size to make the plot smaller
    plt.yscale('log')
    plt.ylabel('Time (ms)')
    plt.xlabel('CCDF')
    plt.title('CCDF of function verification times')
    plt.legend()
    plt.grid()
    plt.savefig(json_file + ".pdf")
    
if __name__ == "__main__":
    main()