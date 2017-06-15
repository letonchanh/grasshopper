from __future__ import absolute_import
from __future__ import print_function
from __future__ import division

import numpy as np


class DataSet(object):

    def __init__(self, fname, num_features, num_examples=None, scale_factors=None):
        with open(fname, 'r') as fin:
            x_indices = []
            x_values = []
            ys = []
            example_id = 0
            for line in fin:
                if num_examples is not None and example_id > num_examples:
                    break
                line = line.strip().split("\t")
                y = int(line[1])
                ys.append(y)
                for feature_pair in line[2:]:
                    f_idx, val = feature_pair.split(':')
                    f_idx = int(f_idx)
                    val = float(val)
                    x_indices.append((example_id, f_idx))
                    x_values.append(val)
                example_id += 1
        self.examples = np.zeros((example_id, num_features))
        self.labels = np.array(ys, dtype=int)
        # Densify the sparse vector
        for ((i, j), v) in zip(x_indices, x_values):
            self.examples[i, j] = v

        self.num_examples = self.examples.shape[0]
        self.num_features = num_features

        self._epochs_completed = 0
        self._index_in_epoch = 0

        # Scale the features. TODO inherit from DataSet and do this in one
        # place
        if scale_factors is None:
            self.scale_factors = np.max(self.examples, axis=0)
            self.scale_factors[self.scale_factors == 0] = 1.0
        else:
            self.scale_factors = scale_factors
        self.examples = self.examples / self.scale_factors

    @property
    def epochs_completed(self):
        return self._epochs_completed

    def next_batch(self, batch_size):
        """Return the next `batch_size` examples from this data set."""
        batch_size = min(batch_size, self.num_examples)
        start = self._index_in_epoch
        self._index_in_epoch += batch_size
        if self._index_in_epoch > self.num_examples:
            # Finished epoch
            self._epochs_completed += 1
            # Shuffle the data
            perm = np.arange(self.num_examples)
            np.random.shuffle(perm)
            self.examples = self.examples[perm]
            self.labels = self.labels[perm]
            # Start next epoch
            start = 0
            self._index_in_epoch = batch_size
            assert batch_size <= self.num_examples
        end = self._index_in_epoch
        return self.examples[start:end], self.labels[start:end]

    def inspect(self, feat_name_to_idx):
        # Flip the feature map
        feat_idx_to_name = {idx:name for name, idx in feat_name_to_idx.items()}

        num_labels = np.max(self.labels) + 1
        idx_to_num_zeros = np.zeros((num_labels, self.num_features))
        idx_to_num_ones = np.zeros((num_labels, self.num_features))

        for i in range(self.num_examples):
            for j in range(self.num_features):
                if self.examples[i, j] < 0.5:
                    idx_to_num_zeros[self.labels[i], j] += 1
                else:
                    idx_to_num_ones[self.labels[i], j] += 1
        idx_to_num_ones /= self.num_examples
        idx_to_num_zeros /= self.num_examples

        for i in range(self.num_features):
            print(feat_idx_to_name.get(i, "UNKNOWN"))
            for j in range(num_labels):
                print("{:8.2f}{:8.2f}".format(
                    100 * idx_to_num_zeros[j, i],
                    100 * idx_to_num_ones[j, i]))
        return


class AddrDataSet(object):

    def __init__(self, fname, num_features, num_examples=None, scale_factors=None):
        """A dataset for training or testing an addr predictor. Constructed from
        a CSV file in the following format:

        EXAMPLE_ID  IS_CHOSEN  PROG_ID,REG_NAME  [FEAT_IDX:VAL]+
        where all spaces are \t characters.
        """
        with open(fname, 'r') as fin:
            x_indices = []
            x_values = []
            ys = []
            example_id = 0
            for line in fin:
                if num_examples is not None and example_id > num_examples:
                    break
                line = line.strip().split("\t")
                ys.append(int(line[1]))
                # Skip line[2] because that's the name of the variable
                for feature_pair in line[3:]:
                    f_idx, val = feature_pair.split(':')
                    f_idx = int(f_idx)
                    val = float(val)
                    x_indices.append((example_id, f_idx))
                    x_values.append(val)
                example_id += 1
        self.examples = np.zeros((example_id, num_features))
        self.labels = np.array(ys, dtype=int)
        # Densify the sparse vector
        for ((i, j), v) in zip(x_indices, x_values):
            self.examples[i, j] = v

        self.num_examples = self.examples.shape[0]
        self.num_features = num_features

        self._epochs_completed = 0
        self._index_in_epoch = 0

        # Scale the features. TODO inherit from DataSet and do this in one
        # place
        if scale_factors is None:
            self.scale_factors = np.max(self.examples, axis=0)
            self.scale_factors[self.scale_factors == 0] = 1.0
        else:
            self.scale_factors = scale_factors
        self.examples = self.examples / self.scale_factors

    @property
    def epochs_completed(self):
        return self._epochs_completed

    def next_batch(self, batch_size):
        """Return the next `batch_size` examples from this data set."""
        batch_size = min(batch_size, self.num_examples)
        start = self._index_in_epoch
        self._index_in_epoch += batch_size
        if self._index_in_epoch > self.num_examples:
            # Finished epoch
            self._epochs_completed += 1
            # Shuffle the data
            perm = np.arange(self.num_examples)
            np.random.shuffle(perm)
            self.examples = self.examples[perm]
            self.labels = self.labels[perm]
            # Start next epoch
            start = 0
            self._index_in_epoch = batch_size
            assert batch_size <= self.num_examples
        end = self._index_in_epoch
        return self.examples[start:end], self.labels[start:end]

    def inspect(self, feat_name_to_idx):
        # Flip the feature map
        feat_idx_to_name = {name:idx for name, idx in feat_name_to_idx.items()}

        num_labels = np.max(self.labels) + 1
        idx_to_num_zeros = np.zeros((num_labels, self.num_features))
        idx_to_num_ones = np.zeros((num_labels, self.num_features))

        for i in range(self.num_examples):
            for j in range(self.num_features):
                if self.examples[i, j] < 0.5:
                    idx_to_num_zeros[self.labels[i], j] += 1
                else:
                    idx_to_num_ones[self.labels[i], j] += 1
        idx_to_num_ones /= self.num_examples
        idx_to_num_zeros /= self.num_examples

        for i in range(self.num_features):
            if i in feat_idx_to_name:
                print("====== " + feat_idx_to_name[i])
                print("{:6s}{:8s}{:8s}".format("Label", "Low", "High"))
                for j in range(num_labels):
                    print("{:2d}{:8.2f}{:8.2f}".format(
                        j,
                        100 * idx_to_num_zeros[j, i],
                        100 * idx_to_num_ones[j, i]))
        return


class IdentDataSet(object):

    def __init__(self, fname, num_features, num_examples=None, scale_factors=None):
        """A dataset for training or testing an ident predictor. Constructed from
        a CSV file in the following format:

        EXAMPLE_ID  IS_CHOSEN  PROG_ID,REG_NAME  [FEAT_IDX:VAL]+
        where all spaces are \t characters.

        Only use the first num_example examples from dataset, if not None.
        """
        # First get line count to be more memory efficient
        # TODO do this for others also
        with open(fname, 'r') as fin:
            num_lines = sum(1 for line in fin)
        self.rows = np.empty((num_lines, num_features))
        self.labels = np.empty(num_lines, dtype=bool)
        self.partitions = np.empty(num_lines, dtype=int)
        self.chosen_rows = np.empty(num_lines, dtype=int)
        self.sparse_idxs = np.empty((num_lines, 2), dtype=int)
        with open(fname, 'r') as fin:
            row_id = 0
            ex_id = 0
            idx_in_example = 0
            for line in fin:
                line = line.strip().split("\t")
                example_num = int(line[0])
                if num_examples is not None and example_num > num_examples:
                    break
                if row_id > 0 and example_num != self.partitions[row_id - 1]:
                    # New example, reset idx_in_example
                    ex_id += 1
                    idx_in_example = 0
                self.sparse_idxs[row_id, 0] = example_num
                self.sparse_idxs[row_id, 1] = idx_in_example
                self.labels[row_id] = line[1] == '1'
                if self.labels[row_id]:
                    self.chosen_rows[ex_id] = idx_in_example
                self.partitions[row_id] = example_num
                # Skip line[2] because that's the name of the variable
                for feature_pair in line[3:]:
                    f_idx, val = feature_pair.split(':')
                    self.rows[row_id, int(f_idx)] = float(val)
                row_id += 1
                idx_in_example += 1
        # Truncate to actual lines read
        self.rows = self.rows[:row_id]
        self.labels = self.labels[:row_id]
        self.partitions = self.partitions[:row_id]
        self.sparse_idxs = self.sparse_idxs[:row_id]
        self.chosen_rows = self.chosen_rows[:ex_id + 1]

        self.num_rows = self.rows.shape[0]
        self.num_features = num_features

        # Keep track of start indices for each partition
        self._start_indices = np.zeros(np.max(self.partitions) + 2, dtype=int)
        self.num_examples = 1
        for i in range(1, self.partitions.shape[0]):
            if self.partitions[i] != self.partitions[i - 1]:
                self._start_indices[self.num_examples] = i
                self.num_examples += 1
        # Add the length at the end to avoid having to check for index out of
        # bounds
        self._start_indices[self.num_examples] = self.partitions.shape[0]

        self._epochs_completed = 0
        self._index_in_epoch = 0
        self._example_ids = np.arange(self.num_examples)

        # Scale the features. TODO inherit from DataSet and do this in one
        # place
        if scale_factors is None:
            self.scale_factors = np.max(self.rows, axis=0)
            self.scale_factors[self.scale_factors == 0] = 1.0
        else:
            self.scale_factors = scale_factors
        self.rows = self.rows / self.scale_factors

    @property
    def epochs_completed(self):
        return self._epochs_completed

    def get_example(self, i):
        """Return the ith example in this data set."""
        s = self._start_indices[i]
        e = self._start_indices[i + 1]
        return self.rows[s:e], self.labels[s:e]

    def next_batch(self, batch_size):
        """Return the next `batch_size` examples from this data set."""
        batch_size = min(batch_size, self.num_examples)
        # These indices are now in self._example_ids
        start = self._index_in_epoch
        self._index_in_epoch += batch_size
        if self._index_in_epoch > self.num_examples:
            # Finished epoch
            self._epochs_completed += 1
            # Shuffle the data
            perm = np.arange(self.num_examples)
            np.random.shuffle(perm)
            self._example_ids = self._example_ids[perm]
            # Start next epoch
            start = 0
            self._index_in_epoch = batch_size
            assert batch_size <= self.num_rows
        end = self._index_in_epoch

        # Construct the batch (TODO improve efficiency?)
        selected_indices = np.zeros(self.num_rows, dtype=bool)
        for example in self._example_ids[start:end]:
            selected_indices[self._start_indices[example]
                             : self._start_indices[example + 1]] = True

        # Construct the sparse_idxs array for this batch
        # Need to reset the row numbers in these indices
        sparse_idxs = np.copy(self.sparse_idxs[selected_indices])
        # The selected examples are given in order of example_id, so sort them
        selected_examples = np.sort(self._example_ids[start:end])

        new_example_id = -1
        last_old_example_id = -1
        for r in xrange(sparse_idxs.shape[0]):
            if sparse_idxs[r, 0] != last_old_example_id:
                new_example_id += 1
                last_old_example_id = sparse_idxs[r, 0]
            sparse_idxs[r, 0] = new_example_id

        return (self.rows[selected_indices],
                self.labels[selected_indices],
                self.chosen_rows[selected_examples],
                sparse_idxs)

    def inspect(self, feat_name_to_idx):
        # Flip the feature map
        feat_idx_to_name = {idx:name for name, idx in feat_name_to_idx.items()}

        idx_to_num_low = np.zeros((2, self.num_features), dtype=int)
        idx_to_num_hi = np.zeros((2, self.num_features), dtype=int)

        for i in range(self.num_rows):
            for j in range(self.num_features):
                if self.rows[i, j] < 0.5:
                    idx_to_num_low[self.labels[i], j] += 1
                else:
                    idx_to_num_hi[self.labels[i], j] += 1

        # num_zero_rows = (self.num_rows - self.num_examples)

        for i in range(self.num_features):
            if i in feat_idx_to_name:
                print("\n====== " + feat_idx_to_name[i])
                print("{:6s}{:>25s}{:>25s}".format("Label", "Low", "High"))
                print("{:<6d}{:>8d}/{:<8d}= {:6.2f}{:>8d}/{:<8d}= {:6.2f}".format(
                    0,
                    idx_to_num_low[0, i],
                    self.num_rows,
                    100 * idx_to_num_low[0, i] / self.num_rows,
                    idx_to_num_hi[0, i],
                    self.num_rows,
                    100 * idx_to_num_hi[0, i] / self.num_rows))
                print("{:<6d}{:>8d}/{:<8d}= {:6.2f}{:>8d}/{:<8d}= {:6.2f}".format(
                    1,
                    idx_to_num_low[1, i],
                    self.num_rows,
                    100 * idx_to_num_low[1, i] / self.num_rows,
                    idx_to_num_hi[1, i],
                    self.num_rows,
                    100 * idx_to_num_hi[1, i] / self.num_rows))
                # print("{:<6d}{:>8d}/{:<8d}= {:6.2f}{:>8d}/{:<8d}= {:6.2f}".format(
                #     0,
                #     idx_to_num_low[0, i],
                #     num_zero_rows,
                #     100 * idx_to_num_low[0, i] / num_zero_rows,
                #     idx_to_num_hi[0, i],
                #     num_zero_rows,
                #     100 * idx_to_num_hi[0, i] / num_zero_rows))
                # print("{:<6d}{:>8d}/{:<8d}= {:6.2f}{:>8d}/{:<8d}= {:6.2f}".format(
                #     1,
                #     idx_to_num_low[1, i],
                #     self.num_examples,
                #     100 * idx_to_num_low[1, i] / self.num_examples,
                #     idx_to_num_hi[1, i],
                #     self.num_examples,
                #     100 * idx_to_num_hi[1, i] / self.num_examples))
        return idx_to_num_hi, idx_to_num_low
