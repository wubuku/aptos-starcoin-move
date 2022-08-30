module starcoin_utils::starcoin_address {
    use std::vector;

    const ERROR_STARCOIN_ADDRESS_LENGTH: u64 = 101;

    struct StarcoinAddress has drop {
        address: vector<u8>,
    }

    public fun new_address(address: vector<u8>): StarcoinAddress {
        assert!(vector::length(&address) == 16, ERROR_STARCOIN_ADDRESS_LENGTH);
        StarcoinAddress {
            address,
        }
    }

    public fun to_bcs_bytes(address: &StarcoinAddress): vector<u8> {
        let i = 0;
        let bs = vector::empty<u8>();
        while (i < vector::length(&address.address)) {
            vector::push_back(&mut bs, *vector::borrow(&address.address, i));
            i = i + 1;
        };
        bs
    }
}