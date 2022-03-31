import os
import sys

from FBG_to_ANTLR import main as fbg_to_antlr
from ANTLR_to_FBG import main as antlr_to_fbg
from BGF_to_FBL import main as bgf_to_fbg
from FBG_to_BGF import main as fbg_to_bgf
from base import read_file_in


fbf = "fbf"
antlr = "antlr"
bgf = "bgf"


def __convert(input_path, output_path, input_format, output_format):
    content = read_file_in(input_path)

    output = None

    if input_format == antlr:
        if output_format == fbf:
            output = antlr_to_fbg(content, input_path)
        elif output_format == bgf:
            fbg = antlr_to_fbg(content, input_path)
            output = fbg_to_bgf(fbg, input_path)

    elif input_format == bgf:
        if output_format == fbf:
            output = bgf_to_fbg(content, input_path)
        elif output_format == antlr:
            fbg = bgf_to_fbg(content, input_path)
            output = fbg_to_antlr(fbg, input_path)

    elif input_format == fbf:
        if output_format == antlr:
            output = fbg_to_antlr(content, input_path)
        elif output_format == bgf:
            output = fbg_to_bgf(content, input_path)

    return output


def convert(input_path, output_path, input_format, output_format = fbf):
    input_format = input_format.lower()
    output_format = output_format.lower()
    if input_path is None:
        raise ValueError("First argument input_path is None")
    if output_path is None:
        raise ValueError("Second argument output_path is None")
    if format is None:
        raise ValueError("Third argument format is None")
    if input_format not in [antlr, bgf, fbf]:
        raise ValueError(f"Unknown input format '{input_format}'")
    if input_format == output_format:
        raise ValueError("input format and output format are equal.")
    if output_format not in [antlr, bgf, fbf]:
        raise ValueError(f"Unknown output format '{output_format}'")

    output = __convert(input_path, output_path, input_format, output_format)

    if output_path is None:
        pass
    elif output_path is "stdout":
        print(output)
    elif output_path == "return":
        return output
    else:
        filename = os.path.basename(input_path)
        output_path += "/" + filename
        if output_format == antlr:
            filename = os.path.basename(output_path)
            path = os.path.dirname(output_path)
            filename = filename.replace(".", "")
            output_path = path + "/" + filename + ".g4"
        else:
            output_path += "." + output_format

        print(f"Saving converted file to {output_path}")

        with open(output_path, 'w') as f:
            f.write(output)


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Bidirectional Conversion Between ANTLR, BGF and a FBF.')
    parser.add_argument('input_path', metavar = 'input-path', type = str, help = 'path to the input grammar')
    parser.add_argument('output_path', metavar = 'output-path', type = str, help = 'path output dir')
    parser.add_argument('input_format', metavar = 'input-format', type = str, help = 'Valid values are: ANTLR, BGF and FBF')
    parser.add_argument('output_format', metavar = 'output-format', type = str, help = 'Valid values are: ANTLR, BGF and FBF')

    args = parser.parse_args()
    status = convert(args.input_path, args.output_path, args.input_format, args.output_format)
    sys.exit(status)