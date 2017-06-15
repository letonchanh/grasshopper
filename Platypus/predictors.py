from __future__ import absolute_import
from __future__ import print_function
from __future__ import division

import os
import time

import numpy as np
import tensorflow as tf


class Predictor(object):

    def __init__(self, model_file, num_features, num_labels, temp=1.0, restore=False):
        self.num_features = num_features
        self.num_labels = num_labels

        # Factors to scale features by
        self._scale_factors = None

        # Make sure model_dir exists
        model_dir = os.path.dirname(model_file)
        if not os.path.exists(model_dir):
            os.makedirs(model_dir)
        self._model_file = model_file
        self._scale_file = model_file + ".scales"

        # Construct the model
        self._graph = tf.Graph()
        self._session = tf.Session(
            graph=self._graph, config=tf.ConfigProto(device_count={"CPU": 1}))
        with tf.device('cpu:0'), self._graph.as_default():
            self._xs = tf.placeholder(
                tf.float32, shape=[None, self.num_features])

            self._ys = tf.placeholder(tf.int32, shape=[None])
            # TODO get rid of actual_y and use sparse_softmax_cross_entropy
            actual_y = tf.one_hot(self._ys, depth=self.num_labels)

            # One layer NN
            hidden_size = 100
            self._W = tf.Variable(tf.random_normal(
                [self.num_features, hidden_size], stddev=0.1))
            self._b = tf.Variable(tf.random_normal([hidden_size], stddev=0.1))
            self._W2 = tf.Variable(tf.random_normal(
                [hidden_size, self.num_labels], stddev=0.1))
            self._b2 = tf.Variable(tf.random_normal(
                [self.num_labels], stddev=0.1))
            # An op to save and restore all variable values
            self._saver = tf.train.Saver(
                [self._W, self._b, self._W2, self._b2], max_to_keep=None)
            activations = tf.matmul(self._xs, self._W) + self._b
            hiddens = tf.nn.relu(activations)
            scores = tf.matmul(hiddens, self._W2) + self._b2

            # Linear model
            # self._W = tf.Variable(tf.random_normal([self.num_features, self.num_labels], stddev=0.1))
            # self._b = tf.Variable(tf.random_normal([self.num_labels], stddev=0.1))
            # # An op to save and restore all variable values
            # self._saver = tf.train.Saver([self._W, self._b], max_to_keep=None)
            # scores = tf.matmul(self._xs, self._W) + self._b

            self._predicted_y = tf.nn.softmax(scores)
            # Add a temperature to predictions to make it more greedy
            temperature = tf.constant(temp, tf.float32)
            self._temp_predicted_y = tf.nn.softmax(scores / temperature)

            self._cross_entropy = tf.reduce_mean(
                tf.nn.softmax_cross_entropy_with_logits(logits=scores, labels=actual_y))
            self._train_step = tf.train.RMSPropOptimizer(0.01, 0.9)\
                .minimize(self._cross_entropy)

            self._prediction = tf.argmax(self._predicted_y, 1)
            correct_prediction = tf.equal(
                self._prediction, tf.argmax(actual_y, 1))
            self._accuracy = tf.reduce_mean(
                tf.cast(correct_prediction, tf.float32))

            self._init = tf.global_variables_initializer()
        if restore:
            self._restore()

    def __del__(self):
        # Close the tf session
        self._session.close()

    def _restore(self, debugMode=False):
        """Restore trained parameters from disk."""
        if debugMode:
            print("Loading model from file %s." % self._model_file)
        self._saver.restore(self._session, self._model_file)

    def train(self, dataset, val_dataset, max_epochs=100, batch_size=100):
        self._session.run(self._init)

        tr_losses, val_losses = [], []
        best_epoch, best_loss = 0, np.Infinity
        last_epoch = 0
        print("Features: %d; # Train: %d; # Val: %d; max_epochs: %d" % (
            dataset.num_features, dataset.num_examples, val_dataset.num_examples,
            max_epochs))
        print("{:>10}{:>10}{:>10}{:>10}{:>10}".format(
            "Epoch", "Tr loss", "Val loss", "Time", "Total"))
        start_run = time.clock()
        start_epoch = start_run
        try:
            while dataset.epochs_completed < max_epochs:
                batch_xs, batch_ys = dataset.next_batch(batch_size)
                self._session.run(self._train_step,
                                  feed_dict={self._xs: batch_xs, self._ys: batch_ys})

                if dataset.epochs_completed != last_epoch:
                    tr_loss = self._session.run(self._cross_entropy,
                                                feed_dict={self._xs: dataset.examples,
                                                           self._ys: dataset.labels})
                    val_loss = self._session.run(self._cross_entropy,
                                                 feed_dict={self._xs: val_dataset.examples,
                                                            self._ys: val_dataset.labels})
                    print("{:>10d}{:>10.4f}{:>10.4f}{:>9.0f}s{:>9.0f}s".format(
                        dataset.epochs_completed, tr_loss, val_loss,
                        time.clock() - start_epoch, time.clock() - start_run))
                    start_epoch = time.clock()
                    tr_losses.append(tr_loss)
                    val_losses.append(val_loss)
                    # Only save model with best validation loss
                    if val_loss < best_loss:
                        best_loss = val_loss
                        best_epoch = dataset.epochs_completed
                        self._saver.save(
                            self._session, self._model_file, write_meta_graph=False)
                    last_epoch = dataset.epochs_completed
        except KeyboardInterrupt:
            print("Interrupted.")

        # Use training data's scale factors
        self._scale_factors = dataset.scale_factors
        np.savetxt(self._scale_file, self._scale_factors)

        print("Choose parameters from epoch %d and saved in file: %s." %
              (best_epoch, self._model_file))
        return tr_losses, val_losses

    def accuracy(self, dataset):
        """Returns the accuracy (fraction of correct predictions) of this model
        on a given dataset."""

        feed_dict = {self._xs: dataset.examples,
                     self._ys: dataset.labels}
        if dataset.num_examples > 0:
            acc = self._session.run(self._accuracy, feed_dict=feed_dict)
        else:
            acc = 0.0
        return acc

    def query(self, features):
        """Ask the model for a prediction on one given example.

        features: list of floats. Assumes dense representation.

        Returns: a vector of shape (num_labels,) of predicted probabilities
        for each possible label.
        """

        if self._scale_factors is None:
            self._scale_factors = np.loadtxt(self._scale_file)
        features = features / self._scale_factors

        feed_dict = {self._xs: np.array([features])}
        return self._session.run(self._temp_predicted_y, feed_dict=feed_dict)[0]

    def get_weights(self):
        """Get the weights and biases that define this model.
        """
        return self._session.run([self._W, self._b])


class AddrPredictor(object):

    def __init__(self, model_file, num_features, restore=False):
        self.num_features = num_features

        # Factors to scale features by
        self._scale_factors = None

        # Make sure model_dir exists
        model_dir = os.path.dirname(model_file)
        if not os.path.exists(model_dir):
            os.makedirs(model_dir)
        self._model_file = model_file
        self._scale_file = model_file + ".scales"

        # Construct the model
        self._graph = tf.Graph()
        self._session = tf.Session(
            graph=self._graph, config=tf.ConfigProto(device_count={"CPU": 1}))
        with tf.device('cpu:0'), self._graph.as_default():
            self._xs = tf.placeholder(
                tf.float32, shape=[None, self.num_features])

            self._ys = tf.placeholder(tf.float32, shape=[None])
            _ys = tf.expand_dims(self._ys, -1)

            # Two layer NN
            hidden_size = 50
            self._W = tf.Variable(tf.random_normal(
                [self.num_features, hidden_size], stddev=0.1))
            self._b = tf.Variable(tf.random_normal([hidden_size], stddev=0.1))
            self._W2 = tf.Variable(tf.random_normal(
                [hidden_size, hidden_size], stddev=0.1))
            self._b2 = tf.Variable(tf.random_normal([hidden_size], stddev=0.1))
            self._W3 = tf.Variable(tf.random_normal(
                [hidden_size, 1], stddev=0.1))
            self._b3 = tf.Variable(tf.random_normal([1], stddev=0.1))
            # An op to save and restore all variable values
            self._saver = tf.train.Saver(
                [self._W, self._b, self._W2, self._b2, self._W3, self._b3], max_to_keep=None)

            hiddens1 = tf.nn.relu(tf.matmul(self._xs, self._W) + self._b)
            hiddens2 = tf.nn.relu(tf.matmul(hiddens1, self._W2) + self._b2)
            self._scores = tf.matmul(hiddens2, self._W3) + \
                self._b3  # num_examples x 1

            # Linear model
            # self._W = tf.Variable(tf.random_normal([self.num_features, 1], stddev=0.1))
            # self._b = tf.Variable(tf.random_normal([1], stddev=0.1))
            # # An op to save and restore all variable values
            # self._saver = tf.train.Saver([self._W, self._b], max_to_keep=None)
            # scores = tf.matmul(self._xs, self._W) + self._b

            _predicted_y = tf.nn.sigmoid(self._scores)
            # # Add a temperature to predictions to make it more greedy
            # temperature = tf.constant(temp, tf.float32)
            # self._temp_predicted_y = tf.nn.sigmoid(scores / temperature)

            self._cross_entropy = tf.reduce_mean(
                tf.nn.sigmoid_cross_entropy_with_logits(logits=self._scores,
                                                        labels=_ys))
            if True:
                self._train_step = tf.train.MomentumOptimizer(0.01, 0.9)\
                    .minimize(self._cross_entropy)
            else:
                self._train_step = tf.train.RMSPropOptimizer(0.01, 0.9)\
                    .minimize(self._cross_entropy)

            self._prediction = tf.round(_predicted_y)
            correct_prediction = tf.equal(self._prediction, _ys)
            self._accuracy = tf.reduce_mean(
                tf.cast(correct_prediction, tf.float32))

            self._init = tf.global_variables_initializer()
        if restore:
            self._restore()

    def __del__(self):
        # Close the tf session
        self._session.close()

    def _restore(self, debugMode=False):
        """Restore trained parameters from disk."""
        if debugMode:
            print("Loading model from file %s." % self._model_file)
        self._saver.restore(self._session, self._model_file)

    def train(self, dataset, val_dataset, max_epochs=100, batch_size=100):
        self._session.run(self._init)

        tr_losses, val_losses = [], []
        best_epoch, best_loss = 0, np.Infinity
        last_epoch = 0
        print("Features: %d; # Train: %d; # Val: %d; max_epochs: %d" % (
            dataset.num_features, dataset.num_examples, val_dataset.num_examples,
            max_epochs))
        print("{:>10}{:>10}{:>10}{:>10}{:>10}".format(
            "Epoch", "Tr loss", "Val loss", "Time", "Total"))
        start_run = time.clock()
        start_epoch = start_run
        try:
            while dataset.epochs_completed < max_epochs:
                batch_xs, batch_ys = dataset.next_batch(batch_size)
                self._session.run(self._train_step,
                                  feed_dict={self._xs: batch_xs, self._ys: batch_ys})

                if dataset.epochs_completed != last_epoch:
                    tr_loss = self._session.run(self._cross_entropy,
                                                feed_dict={self._xs: dataset.examples,
                                                           self._ys: dataset.labels})
                    val_loss = self._session.run(self._cross_entropy,
                                                 feed_dict={self._xs: val_dataset.examples,
                                                            self._ys: val_dataset.labels})
                    print("{:>10d}{:>10.4f}{:>10.4f}{:>9.0f}s{:>9.0f}s".format(
                        dataset.epochs_completed, tr_loss, val_loss,
                        time.clock() - start_epoch, time.clock() - start_run))
                    start_epoch = time.clock()
                    tr_losses.append(tr_loss)
                    val_losses.append(val_loss)
                    # Only save model with best validation loss
                    if val_loss < best_loss:
                        best_loss = val_loss
                        best_epoch = dataset.epochs_completed
                        self._saver.save(
                            self._session, self._model_file, write_meta_graph=False)
                    last_epoch = dataset.epochs_completed
        except KeyboardInterrupt:
            print("Interrupted.")

        # Use training data's scale factors
        self._scale_factors = dataset.scale_factors
        np.savetxt(self._scale_file, self._scale_factors)

        print("Choose parameters from epoch %d and saved in file: %s." %
              (best_epoch, self._model_file))
        return tr_losses, val_losses

    def accuracy(self, dataset):
        """Returns the accuracy (fraction of correct predictions) of this model
        on a given dataset."""

        feed_dict = {self._xs: dataset.examples,
                     self._ys: dataset.labels}
        if dataset.num_examples > 0:
            acc = self._session.run(self._accuracy, feed_dict=feed_dict)
        else:
            acc = 0.0
        return acc

    def query(self, features):
        """Ask the model for a prediction on one given example.

        features: array of shape (num_addrs, num_features). Assumes dense representation.

        Returns: a vector of shape (num_addrs,) of predicted probabilities
        for each possible label.
        """

        if self._scale_factors is None:
            self._scale_factors = np.loadtxt(self._scale_file)
        features = features / self._scale_factors

        feed_dict = {self._xs: np.array(features)}
        scores = self._session.run(self._scores, feed_dict=feed_dict)
        return np.ndarray.flatten(scores)

    def get_weights(self):
        """Get the weights and biases that define this model.
        """
        return self._session.run([self._W, self._b])


class IdentPredictor(object):

    def __init__(self, model_file, num_features, temp=1.0, restore=False):
        self.num_features = num_features
        self.max_num_idents = 20  # TODO get this from hypers

        # Factors to scale features by
        self._scale_factors = None

        # Make sure model_dir exists
        model_dir = os.path.dirname(model_file)
        if not os.path.exists(model_dir):
            os.makedirs(model_dir)
        self._model_file = model_file
        self._scale_file = model_file + ".scales"

        # Construct the model
        self._graph = tf.Graph()
        self._session = tf.Session(
            graph=self._graph, config=tf.ConfigProto(device_count={"CPU": 1}))
        with tf.device('cpu:0'), self._graph.as_default():
            # ---------- The inputs
            # Let num_rows = \sum_{examples} num-vars-in-example
            # A batch has shape = [num_rows, num_features]
            self._rows = tf.placeholder(
                tf.float32, shape=[None, self.num_features])
            # True if this row is the chosen ident, [num_rows,]
            self._labels = tf.placeholder(tf.bool, shape=[None])
            # Index of chosen idents, [num_examples,]
            self._chosen_rows = tf.placeholder(tf.int64, shape=[None])
            # (example_idx, ident_idx) for every choice for every production
            # Shape: [num_rows, 2]
            self._sparse_idxs = tf.placeholder(tf.int64, shape=[None, 2])

            # ---------- The weights that define the model: two layer NN
            hidden_size = 50
            self._W = tf.Variable(tf.random_normal(
                [self.num_features, hidden_size], stddev=0.1))
            self._b = tf.Variable(tf.random_normal([hidden_size], stddev=0.1))
            self._W2 = tf.Variable(tf.random_normal(
                [hidden_size, hidden_size], stddev=0.1))
            self._b2 = tf.Variable(tf.random_normal([hidden_size], stddev=0.1))
            self._W3 = tf.Variable(tf.random_normal(
                [hidden_size, 1], stddev=0.1))
            self._b3 = tf.Variable(tf.random_normal([1], stddev=0.1))
            # An op to save and restore all variable values
            self._saver = tf.train.Saver(
                [self._W, self._b, self._W2, self._b2, self._W3, self._b3], max_to_keep=None)

            # Linear regressions
            #self._W = tf.Variable(tf.random_normal([self.num_features, 1], stddev=0.1))
            #self._b = tf.Variable(tf.random_normal([1], stddev=0.1))
            # # An op to save and restore all variable values
            # self._saver = tf.train.Saver([self._W, self._b], max_to_keep=None)

            # ----------- The model
            num_examples = tf.shape(self._chosen_rows)[0]

            hiddens1 = tf.nn.relu(tf.matmul(self._rows, self._W) + self._b)
            hiddens2 = tf.nn.relu(tf.matmul(hiddens1, self._W2) + self._b2)
            # Scores of shape [num_rows,] for every variable in all examples
            scores_values = tf.reshape(
                tf.matmul(hiddens2, self._W3) + self._b3, [-1])
            scores_shape = tf.to_int64(tf.stack([num_examples, self.max_num_idents]))

            # [num_examples, max_num_idents]
            sparse_scores = tf.SparseTensor(
                indices=self._sparse_idxs,
                values=scores_values,
                dense_shape=scores_shape)

            # [num_examples, max_num_idents]
            sparse_probs = tf.sparse_softmax(sparse_scores)
            self._temp_probs = tf.sparse_tensor_to_dense(
                tf.sparse_softmax(sparse_scores / temp))
            gt_probs = tf.sparse_retain(sparse_probs, self._labels)

            # implement a safe log, where log(x) = log(eps + x)
            gt_probs = gt_probs.values + 1e-6
            gt_logprobs = tf.log(gt_probs)
            self._cross_entropy = -1.0 * tf.reduce_sum(gt_logprobs) / tf.to_float(num_examples)

            # [num_examples, max_num_idents]
            dense_probs = tf.sparse_tensor_to_dense(sparse_probs)
            accuracies = tf.equal(tf.argmax(dense_probs, axis=1),
                                  self._chosen_rows)
            self._accuracy = tf.reduce_mean(tf.to_float(accuracies))

            if True:
                self._train_step = tf.train.MomentumOptimizer(0.01, 0.9)\
                    .minimize(self._cross_entropy)
            else:
                self._train_step = tf.train.RMSPropOptimizer(0.01, 0.9)\
                    .minimize(self._cross_entropy)

            self._init = tf.global_variables_initializer()
        if restore:
            self._restore()

    def __del__(self):
        # Close the tf session
        self._session.close()

    def _restore(self, debugMode=False):
        """Restore trained parameters from disk."""
        if debugMode:
            print("Loading model from file %s." % self._model_file)
        self._saver.restore(self._session, self._model_file)

    def accuracy(self, dataset):
        """Returns the accuracy (fraction of correct predictions) of this model on a given dataset.
        """
        feed_dict = {self._rows: dataset.rows,
                     self._labels: dataset.labels,
                     self._chosen_rows: dataset.chosen_rows,
                     self._sparse_idxs: dataset.sparse_idxs}
        if dataset.num_examples > 0:
            acc = self._session.run(self._accuracy, feed_dict=feed_dict)
        else:
            acc = 0.0
        return acc

    def cross_entropy(self, dataset):
        """Returns the cross entropy of this model on a given dataset."""
        feed_dict = {self._rows: dataset.rows,
                     self._labels: dataset.labels,
                     self._chosen_rows: dataset.chosen_rows,
                     self._sparse_idxs: dataset.sparse_idxs}
        return self._session.run(self._cross_entropy, feed_dict=feed_dict)

    def train(self, dataset, val_dataset, max_epochs=100, batch_size=100):
        self._session.run(self._init)

        tr_losses, val_losses = [], []
        best_epoch, best_loss = 0, np.Infinity
        last_epoch = 0
        print("Features: %d; # Train: %d; # Val: %d; max_epochs: %d" % (
            dataset.num_features, dataset.num_examples, val_dataset.num_examples,
            max_epochs))
        print("{:>10}{:>10}{:>10}{:>10}{:>10}".format(
            "Epoch", "Tr loss", "Val loss", "Time", "Total"))
        start_run = time.clock()
        start_epoch = start_run
        try:
            while dataset.epochs_completed < max_epochs:
                rows, labels, chosen_rows, sparse_idxs = dataset.next_batch(batch_size)
                self._session.run(self._train_step,
                                  feed_dict={self._rows: rows,
                                             self._labels: labels,
                                             self._chosen_rows: chosen_rows,
                                             self._sparse_idxs: sparse_idxs})
                if dataset.epochs_completed != last_epoch:
                    tr_loss = self.cross_entropy(dataset)
                    val_loss = self.cross_entropy(val_dataset)
                    print("{:>10d}{:>10.4f}{:>10.4f}{:>9.0f}s{:>9.0f}s".format(
                        dataset.epochs_completed, tr_loss, val_loss,
                        time.clock() - start_epoch, time.clock() - start_run))

                    start_epoch = time.clock()
                    tr_losses.append(tr_loss)
                    val_losses.append(val_loss)
                    # Only save model with best validation loss
                    if val_loss < best_loss:
                        best_loss = val_loss
                        best_epoch = dataset.epochs_completed
                        self._saver.save(
                            self._session, self._model_file, write_meta_graph=False)

                    last_epoch = dataset.epochs_completed
        except KeyboardInterrupt:
            print("Interrupted.")

        # Use training data's scale factors
        self._scale_factors = dataset.scale_factors
        np.savetxt(self._scale_file, self._scale_factors)

        print("Choose parameters from epoch %d and saved in file: %s." %
              (best_epoch, self._model_file))
        return tr_losses, val_losses

    def query(self, example):
        """Ask the model for a prediction on one given example.

        example: array of shape (num_vars, num_features). Assumes dense representation.

        Returns: a vector of shape (num_vars,) of predicted probabilities
        for each possible variable.
        """
        if example.shape[0] > self.max_num_idents:
            assert 0 and "Too many ident candidates - increase self.max_num_idents!"

        if self._scale_factors is None:
            self._scale_factors = np.loadtxt(self._scale_file)
        example = example / self._scale_factors

        feed_dict = {self._rows: example,
                     self._chosen_rows: [0],
                     self._sparse_idxs: [(0, i) for i in xrange(example.shape[0])]}
        return self._session.run(self._temp_probs, feed_dict=feed_dict)[0][:example.shape[0]]
