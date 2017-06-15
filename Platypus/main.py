from __future__ import absolute_import
from __future__ import print_function
from __future__ import division

import argparse
import traceback
import pdb
import os
import re
import sys
import json
# import cProfile
import numpy as np

import predictors as ps
import dataset as ds
import hypers as hs


# Don't use any GPUs:
os.environ["CUDA_VISIBLE_DEVICES"] = ""

# Some functions to manage the data and model files


def get_model_file(model_dir, nonterminal):
    return os.path.join(model_dir, "predictors", nonterminal)


def get_metadata_file(data_dir):
    return os.path.join(data_dir, "metadata.csv")


def get_train_files(data_dir):
    regex = re.compile(r"train_([\w-]+)_data\.csv$")
    for f in sorted(os.listdir(data_dir)):
        m = regex.match(f)
        if m:
            yield m.group(1), os.path.join(data_dir, f)


def get_train_file(data_dir, nonterminal):
    return os.path.join(data_dir, "train_%s_data.csv" % nonterminal)


def get_val_file(data_dir, nonterminal):
    return os.path.join(data_dir, "val_%s_data.csv" % nonterminal)


def get_test_file(data_dir, nonterminal):
    return os.path.join(data_dir, "test_%s_data.csv" % nonterminal)


def read_metadata(data_dir):
    """Read in metadata about nonterminals, feature index maps, etc"""
    with open(get_metadata_file(data_dir)) as fin:
        metadata = json.load(fin)

    return metadata


def train_models(data_dir, nonterminals=None, model_dir=None):
    # Make sure data exists
    assert os.path.exists(data_dir)
    # Create directory to store trained model params
    if model_dir is None:
        import datetime
        model_dir = os.path.normpath(os.path.join(
            data_dir, "../../models", datetime.datetime.now().strftime("%Y-%m-%d-%H-%M/")))
        if os.path.exists(model_dir):
            from random import choice
            from string import lowercase
            model_dir += "".join(choice(lowercase) for i in range(4))
    if not os.path.exists(model_dir):
        os.makedirs(model_dir)
    print("Storing model in " + model_dir)

    # Copy all files needed at prediction time to this dir:
    # productionStore and FeatureMap needed by F#
    from shutil import copy
    regex = re.compile(r".*\.xml\.gz$")
    for f in filter(regex.match, os.listdir(data_dir)):
        copy(os.path.join(data_dir, f), model_dir)
    # metadata needed by query()
    copy(get_metadata_file(data_dir), model_dir)

    hypers = hs.flat
    with open(os.path.join(model_dir, "hypers.json"), 'w') as f:
        json.dump({"defaults": hypers.defaults, "specifics": hypers.specifics}, f)

    metadata = read_metadata(data_dir)
    num_features = metadata["generic_num_features"]
    nonterm_to_num_labels = metadata["nonterm_to_num_labels"]
    ident_to_num_features = metadata["ident_to_num_features"]

    # Store some information to plot
    acc_of_nonterm = {}
    dataset_size_of_nonterm = {}
    losses_of_nonterm = {}

    if nonterminals is None or nonterminals is []:
        nonterminals = get_train_files(data_dir)
    else:
        nonterminals = [(n, get_train_file(data_dir, n)) for n in nonterminals]

    for nonterminal, f in nonterminals:
        # Load data and create model based on type of nonterminal
        if nonterminal in nonterm_to_num_labels:
            print("\nTraining model for %s" % (nonterminal,))
            train_data = ds.DataSet(f, metadata["generic_num_features"],
                                    num_examples=hypers.get("truncate_train", nonterminal))
            val_data = ds.DataSet(get_val_file(data_dir, nonterminal),
                                  num_features, scale_factors=train_data.scale_factors,
                                  num_examples=hypers.get("truncate_val", nonterminal))
            test_data = ds.DataSet(get_test_file(data_dir, nonterminal),
                                   num_features, scale_factors=train_data.scale_factors,
                                   num_examples=hypers.get("truncate_val", nonterminal))

            p = ps.Predictor(get_model_file(model_dir, nonterminal),
                             num_features, nonterm_to_num_labels[nonterminal])
        elif nonterminal == 'addr':
            print("\nTraining Variable addr model for %s" % (nonterminal,))
            train_data = ds.AddrDataSet(f, ident_to_num_features[nonterminal],
                                        num_examples=hypers.get("truncate_train", nonterminal))
            val_data = ds.AddrDataSet(get_val_file(data_dir, nonterminal),
                                      ident_to_num_features[nonterminal],
                                      scale_factors=train_data.scale_factors,
                                      num_examples=hypers.get("truncate_val", nonterminal))
            test_data = ds.AddrDataSet(get_test_file(data_dir, nonterminal),
                                       ident_to_num_features[nonterminal],
                                       scale_factors=train_data.scale_factors,
                                       num_examples=hypers.get("truncate_val", nonterminal))

            p = ps.AddrPredictor(get_model_file(model_dir, nonterminal),
                                 ident_to_num_features[nonterminal])
        elif nonterminal in ident_to_num_features:
            print("\nTraining Variable model for %s" % (nonterminal,))
            train_data = ds.IdentDataSet(f, ident_to_num_features[nonterminal],
                                         num_examples=hypers.get("truncate_train", nonterminal))
            val_data = ds.IdentDataSet(get_val_file(data_dir, nonterminal),
                                       ident_to_num_features[nonterminal],
                                       scale_factors=train_data.scale_factors,
                                       num_examples=hypers.get("truncate_val", nonterminal))
            test_data = ds.IdentDataSet(get_test_file(data_dir, nonterminal),
                                        ident_to_num_features[nonterminal],
                                        scale_factors=train_data.scale_factors,
                                        num_examples=hypers.get("truncate_val", nonterminal))

            p = ps.IdentPredictor(get_model_file(model_dir, nonterminal),
                                  ident_to_num_features[nonterminal])
        else:
            # These are trivial nonterminals, so continue
            print("Skipping nonterminal %s" % (nonterminal,))
            continue

        # Train the model and collect loss & accuracy info
        losses = p.train(train_data, val_data,
                         max_epochs=hypers.get("max_epochs", nonterminal),
                         batch_size=hypers.get("batch_size", nonterminal))

        losses_of_nonterm[nonterminal] = losses
        acc_of_nonterm[nonterminal] = (p.accuracy(val_data),
                                       p.accuracy(test_data))

        # Delete the predictor to close the sessions right away
        del p
        dataset_size_of_nonterm[nonterminal] = (train_data.num_examples,
                                                val_data.num_examples,
                                                test_data.num_examples)

    with open(os.path.join(model_dir, "summary.txt"), "a") as fout:
        def print_both(s):
            print(s)
            fout.write(s)
        print_both("\n\n--------------------")
        print_both("{:20}{:>12}{:>12}{:>12}{:>12}{:>12}{:>12}{:>12}\n".format(
            "Nonterminal",
            "#Train", "#Val", "#Test",
            "Val %", "Test %", "Best epoch", "Val loss"))
        for nonterm in sorted(acc_of_nonterm):
            print_both("{:20}{:12d}{:12d}{:12d}{:12.4f}{:12.4f}{:12d}{:12.4f}".format(
                nonterm,
                dataset_size_of_nonterm[nonterm][0],
                dataset_size_of_nonterm[nonterm][1],
                dataset_size_of_nonterm[nonterm][2],
                100 * acc_of_nonterm[nonterm][0],
                100 * acc_of_nonterm[nonterm][1],
                np.argmin(losses_of_nonterm[nonterm][1]) + 1,
                np.min(losses_of_nonterm[nonterm][1])))

        # Compute average validation loss across dataset
        sum_of_losses = 0.0
        dataset_size = 0
        for nonterm in acc_of_nonterm:
            sum_of_losses += (np.min(losses_of_nonterm[nonterm][1])
                            * dataset_size_of_nonterm[nonterm][1])
            dataset_size += dataset_size_of_nonterm[nonterm][1]
        print_both("Average validation loss: %.4f" % (sum_of_losses / dataset_size))

        # Plot the train/val losses
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.backends.backend_pdf import PdfPages

        plotfilename = os.path.join(model_dir, "training-losses.pdf")
        while os.path.exists(plotfilename):
            plotfilename = plotfilename[:-4] + "1.pdf"

        with PdfPages(plotfilename) as pdf:
            for nonterm in sorted(losses_of_nonterm):
                tr, val = losses_of_nonterm[nonterm]
                plt.title(nonterm + ": Val %.2f %%, Test %.2f %%" % (
                    100 * acc_of_nonterm[nonterm][0],
                    100 * acc_of_nonterm[nonterm][1],
                ))
                plt.xlabel("Epochs")
                plt.ylabel("Cross entropy")
                plt.plot(tr, 'b-', label="Training loss")
                plt.plot(val, 'r-', label="Validation loss")
                plt.legend()
                plt.grid(True)
                pdf.savefig()
                plt.close()
        print_both("\nSaved training/validation losses to %s" % plotfilename)
    return


def query(model_dir, temperature):

    metadata = read_metadata(model_dir)
    num_features = metadata["generic_num_features"]
    nonterm_to_num_labels = metadata["nonterm_to_num_labels"]
    ident_to_num_features = metadata["ident_to_num_features"]

    # Create all the predictors ahead of time so we can re-use their sessions
    predictors = {}
    for (nonterm, num_labels) in nonterm_to_num_labels.items():
        predictors[nonterm] = ps.Predictor(get_model_file(model_dir, nonterm),
                                           num_features, num_labels,
                                           temperature, True)
    variable_predictors = {}
    for (ident, num_features) in ident_to_num_features.items():
        if ident == 'addr':
            variable_predictors[ident] = ps.AddrPredictor(
                get_model_file(model_dir, ident), num_features,
                True)
        else:
            variable_predictors[ident] = ps.IdentPredictor(
                get_model_file(model_dir, ident), num_features,
                temperature, True)

    while True:
        try:
            query_type = raw_input().split(" ")
        except EOFError:
            break
        if query_type[0] == "GENERIC":
            query_list = raw_input().strip().split(" ")
            nonterminal = query_list[0]
            features = np.array(query_list[1:], dtype=float)

            res = predictors[nonterminal].query(features)
            print(" ".join(map(str, res)))
            sys.stdout.flush()
        elif query_type[0] == "VARIABLE":
            assert len(query_type) == 4
            num_rows = int(query_type[1])
            ident = query_type[2]
            num_features = int(query_type[3])

            example = np.zeros((num_rows, num_features))
            for i in range(num_rows):
                row = raw_input().strip().split(" ")
                assert len(row) == num_features
                for j, rowj in enumerate(row):
                    example[i, j] = float(rowj)

            res = variable_predictors[ident].query(example)
            print(" ".join(map(str, res)))
            sys.stdout.flush()

    return


def plot_weights(W, b, feat_labels, prod_labels):
    plt.clf()
    fig, ax = plt.subplots()
    heatmap = ax.pcolor(W.transpose(), cmap=plt.cm.RdBu)

    # put the major ticks at the middle of each cell
    ax.set_xticks(np.arange(W.shape[0]) + 0.5, minor=False)
    ax.set_yticks(np.arange(W.shape[1]) + 0.5, minor=False)

    # want a more natural, table-like display
    # ax.invert_yaxis()
    # ax.xaxis.tick_top()

    ax.set_xticklabels(feat_labels, minor=False)
    ax.set_yticklabels(prod_labels, minor=False)
    # Make the x ticks vertical
    plt.xticks(rotation=90)
    # Increase the space below for the axis labels
    fig.subplots_adjust(bottom=0.3)

    plt.show()


def inspect_models(model_dir):
    metadata = read_metadata(model_dir)
    num_features = metadata["generic_num_features"]
    nonterm_to_num_labels = metadata["nonterm_to_num_labels"]
    feature_idx_to_name = metadata["generic_feature_map"]

    for (nonterm, num_labels) in nonterm_to_num_labels.items():
        p = ps.Predictor(get_model_file(model_dir, nonterm),
                         num_features, num_labels, 1.0, True)
        W, b = p.get_weights()

        prod_labels = [str(i) for i in range(W.shape[1])]
        feat_labels = [feature_idx_to_name.get(
            i, "") for i in range(W.shape[0])]
        # TODO call plot_weights here and save to file
    return


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Tensorflow backend for Wombat.")
    run_modes = parser.add_mutually_exclusive_group(required=True)
    run_modes.add_argument("--train", action="store_true")
    run_modes.add_argument("--query", action="store_true")

    parser.add_argument("-d", "--datadir", type=str,
                        default="data/2vars_1nesting/modelTraining/",
                        help="directory containing the training data")
    parser.add_argument("-m", "--modeldir", type=str,
                        help="directory containing the trained model parameters")
    parser.add_argument("-n", "--nonterminal", type=str, nargs="+",
                        help="only train models for specified nonterminals")
    parser.add_argument("-t", "--temperature", type=float, default=1.0,
                        help="Temperature with which to query")
    args = parser.parse_args()

    try:
        if args.train:
            train_models(args.datadir, nonterminals=args.nonterminal, model_dir=args.modeldir)
        elif args.query:
            assert args.modeldir is not None, "Need to specify --modeldir"
            # cProfile.run("query(args.datadir, args.temperature)", "query.stats")
            query(args.modeldir, args.temperature)
    except:
        _, _, tb = sys.exc_info()
        traceback.print_exc()
        pdb.post_mortem(tb)
