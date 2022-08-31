module starcoin_utils::starcoin_verifier {
    use starcoin_utils::bcs_deserializer;
    use starcoin_utils::bit;
    use starcoin_utils::starcoin_address;
    use starcoin_utils::structured_hash;
    use std::hash;
    use std::option;
    use std::vector;

    const HASH_LEN_IN_BITS: u64 = 32 * 8;
    const SPARSE_MERKLE_LEAF_NODE: vector<u8> = b"SparseMerkleLeafNode";
    const SPARSE_MERKLE_INTERNAL_NODE: vector<u8> = b"SparseMerkleInternalNode";
    const BLOB_HASH_PREFIX: vector<u8> = b"Blob";
    const DEFAULT_VALUE: vector<u8> = x"";
    const ACCOUNT_STORAGE_INDEX_RESOURCE: u64 = 1;
    const ERROR_ACCOUNT_STORAGE_ROOTS: u64 = 101;
    const ERROR_LITERAL_HASH_WRONG_LENGTH: u64 = 102;
    const ERROR_ACCUMULATOR_PROOF_TOO_LONG: u64 = 103;
    const SPARSE_MERKLE_PLACEHOLDER_HASH_LITERAL: vector<u8> = b"SPARSE_MERKLE_PLACEHOLDER_HASH";


    struct AccountState has store, drop, copy {
        storage_roots: vector<option::Option<vector<u8>>>,
    }

    public fun bcs_deserialize_account_state(data: &vector<u8>): AccountState {
        let (vec, _) = bcs_deserializer::deserialize_option_bytes_vector(data, 0);
        AccountState {
            storage_roots: vec
        }
    }

    struct StateProof has store, drop, copy {
        /**
        * Account state's proof for global state root.
        */
        account_proof: SparseMerkleProof,
        /**
         * Account state including storage roots.
         */
        account_state: vector<u8>,
        /**
         * State's proof for account storage root.
         */
        proof: SparseMerkleProof,
    }

    public fun new_state_proof(account_proof: SparseMerkleProof, account_state: vector<u8>, proof: SparseMerkleProof): StateProof {
        StateProof {
            account_proof,
            account_state,
            proof,
        }
    }

    struct SparseMerkleProof has store, drop, copy {
        siblings: vector<vector<u8>>,
        leaf: SMTNode,
    }

    public fun new_sparse_merkle_proof(siblings: vector<vector<u8>>, leaf: SMTNode): SparseMerkleProof {
        SparseMerkleProof {
            siblings,
            leaf,
        }
    }

    struct SMTNode has store, drop, copy {
        hash1: vector<u8>,
        hash2: vector<u8>,
    }

    public fun new_smt_node(hash1: vector<u8>, hash2: vector<u8>): SMTNode {
        SMTNode {
            hash1,
            hash2,
        }
    }

    public fun empty_smt_node(): SMTNode {
        SMTNode {
            hash1: vector::empty(),
            hash2: vector::empty(),
        }
    }

    struct AccumulatorProof has store, drop, copy {
        siblings: vector<vector<u8>>,
    }

    public fun new_accumulator_proof(siblings: vector<vector<u8>>): AccumulatorProof {
        AccumulatorProof {
            siblings,
        }
    }

    public fun verify_resource_state_proof(state_proof: &StateProof, state_root: &vector<u8>,
                                           account_address: &starcoin_address::Address, resource_struct_tag: &vector<u8>,
                                           state: &vector<u8>): bool {
        let accountState: AccountState = bcs_deserialize_account_state(&state_proof.account_state);
        assert!(vector::length(&accountState.storage_roots) > ACCOUNT_STORAGE_INDEX_RESOURCE, ERROR_ACCOUNT_STORAGE_ROOTS);
        //
        // First, verify state for storage root.
        //
        let storageRoot = option::borrow(vector::borrow(&accountState.storage_roots, ACCOUNT_STORAGE_INDEX_RESOURCE));
        let ok: bool = verify_sm_proof_by_key_value(&state_proof.proof.siblings,
            &state_proof.proof.leaf,
            storageRoot,
            resource_struct_tag, // resource struct tag BCS serialized as key
            state);
        if (!ok) {
            return false
        };
        //
        // Then, verify account state for global state root.
        //
        ok = verify_sm_proof_by_key_value(&state_proof.account_proof.siblings,
            &state_proof.account_proof.leaf,
            state_root,
            &starcoin_address::to_bcs_bytes(account_address), // Starcoin account address as key
            &state_proof.account_state,
        );
        ok
    }

    /// Verify sparse merkle proof by key and value.
    public fun verify_sm_proof_by_key_value(side_nodes: &vector<vector<u8>>, leaf_data: &SMTNode, expected_root: &vector<u8>, key: &vector<u8>, value: &vector<u8>): bool {
        let path = hash_key(key);
        let current_hash: vector<u8>;
        if (*value == DEFAULT_VALUE) {
            // Non-membership proof.
            if (empty_smt_node() == *leaf_data) {
                current_hash = placeholder();
            } else {
                if (*&leaf_data.hash1 == *&path) {
                    return false
                };
                if (!(bit::count_common_prefix(&leaf_data.hash1, &path) >= vector::length(side_nodes))) {
                    return false
                };
                current_hash = structured_hash::hash(SPARSE_MERKLE_LEAF_NODE, leaf_data);
            };
        } else {
            // Membership proof.
            if (empty_smt_node() == *leaf_data) {
                return false
            };
            if (*&leaf_data.hash1 != *&path) {
                return false
            };
            let value_hash = hash_value(value);
            if (*&leaf_data.hash2 != value_hash) {
                return false
            };
            current_hash = structured_hash::hash(SPARSE_MERKLE_LEAF_NODE, leaf_data);
        };

        current_hash = compute_sm_root_by_path_and_node_hash(side_nodes, &path, &current_hash);
        current_hash == *expected_root
    }

    public fun compute_sm_root_by_path_and_node_hash(side_nodes: &vector<vector<u8>>, path: &vector<u8>, node_hash: &vector<u8>): vector<u8> {
        let current_hash = *node_hash;
        let i = 0;
        let proof_length = vector::length(side_nodes);
        while (i < proof_length) {
            let sibling = *vector::borrow(side_nodes, i);
            let bit = bit::get_bit_at_from_msb(path, proof_length - i - 1);
            let internal_node = if (bit) {
                SMTNode { hash1: sibling, hash2: current_hash }
            } else {
                SMTNode { hash1: current_hash, hash2: sibling }
            };
            current_hash = structured_hash::hash(SPARSE_MERKLE_INTERNAL_NODE, &internal_node);
            i = i + 1;
        };
        current_hash
    }

    public fun placeholder(): vector<u8> {
        create_literal_hash(&SPARSE_MERKLE_PLACEHOLDER_HASH_LITERAL)
    }

    public fun create_literal_hash(word: &vector<u8>): vector<u8> {
        if (vector::length(word)  <= 32) {
            let zero_len = 32 - vector::length(word);
            let i = 0;
            let r = *word;
            while (i < zero_len) {
                vector::push_back(&mut r, 0);
                i = i + 1;
            };
            return r
        };
        abort ERROR_LITERAL_HASH_WRONG_LENGTH
    }

    fun hash_key(key: &vector<u8>): vector<u8> {
        hash::sha3_256(*key)
    }

    fun hash_value(value: &vector<u8>): vector<u8> {
        structured_hash::hash(BLOB_HASH_PREFIX, value)
    }


    public fun verify_accumulator(proof: &AccumulatorProof, expected_root: &vector<u8>, hash: &vector<u8>, index: u64): bool {
        let length = vector::length(&proof.siblings);
        assert!(length <= 63, ERROR_ACCUMULATOR_PROOF_TOO_LONG);
        let current_idx = index;
        let current_hash = *hash;
        let i = 0;
        while (i < length) {
            //debug::print(&current_idx);
            //debug::print(&current_hash);
            let s = vector::borrow(&proof.siblings, i);
            current_hash = internal_hash(current_idx, &current_hash, s);
            current_idx = current_idx / 2;
            i = i + 1;
        };
        //debug::print(&current_hash);
        current_hash == *expected_root
    }

    fun internal_hash(index: u64, element: &vector<u8>, sibling: &vector<u8>): vector<u8> {
        if (index % 2 == 0) {
            parent_hash(element, sibling)
        } else {
            parent_hash(sibling, element)
        }
    }

    fun parent_hash(left: &vector<u8>, right: &vector<u8>): vector<u8> {
        //debug::print(left);
        //debug::print(right);
        let c = concat(*left, *right);
        hash::sha3_256(c)
    }

    fun concat(v1: vector<u8>, v2: vector<u8>): vector<u8> {
        vector::append(&mut v1, v2);
        v1
    }
}
