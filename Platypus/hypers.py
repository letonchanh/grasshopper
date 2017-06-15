

class Hypers(object):

    def __init__(self, defaults, specifics):
        self.defaults = defaults
        self.specifics = specifics

    def get(self, name, nonterminal=None):
        if nonterminal is None \
                or nonterminal not in self.specifics \
                or name not in self.specifics[nonterminal]:
            return self.defaults[name]
        return self.specifics[nonterminal][name]


flat = Hypers(
    {
        "max_epochs": 200,
        "batch_size": 500,
        "truncate_train": 1e6,
        "truncate_val": 1e6,
        "hidden_dim": 100,
    },
    {
        "addr": {
            "max_epochs": 100,
            "hidden_dim": 50,
        },
        "expr_ls_0": {
            "hidden_dim": 50,
        },
        "expr_ls_1": {
            "hidden_dim": 50,
        },
        "expr_tree_0": {
            "hidden_dim": 50,
        },
    }
)
