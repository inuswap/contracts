// File: @openzeppelin/contracts/math/SafeMath.sol

pragma solidity ^0.4.20;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}
// Abstract contract for the full ERC 20 Token standard
// https://github.com/ethereum/EIPs/issues/20
pragma solidity ^0.4.8;

contract Token {
    /* This is a slight change to the ERC20 base standard.
    function totalSupply() view returns (uint256 supply);
    is replaced with:
    uint256 public totalSupply;
    This automatically creates a getter function for the totalSupply.
    This is moved to the base contract since public getter functions are not
    currently recognised as an implementation of the matching abstract
    function by the compiler.
    */
    /// total amount of tokens
    uint256 public totalSupply;

    /// @param _owner The address from which the balance will be retrieved
    /// @return The balance
    function balanceOf(address _owner)  public view returns (uint256 balance);

    /// @notice send `_value` token to `_to` from `msg.sender`
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    function transfer(address _to, uint256 _value) public returns (bool success);

    /// @notice send `_value` token to `_to` from `_from` on the condition it is approved by `_from`
    /// @param _from The address of the sender
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    function transferFrom(address _from, address _to, uint256 _value) public returns (bool success);

    /// @notice `msg.sender` approves `_spender` to spend `_value` tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @param _value The amount of tokens to be approved for transfer
    /// @return Whether the approval was successful or not
    function approve(address _spender, uint256 _value) public returns (bool success);

    /// @param _owner The address of the account owning tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @return Amount of remaining tokens allowed to spent
    function allowance(address _owner, address _spender) public view returns (uint256 remaining);

    event Transfer(address indexed _from, address indexed _to, uint256 _value);
    event Approval(address indexed _owner, address indexed _spender, uint256 _value);
}
/*
You should inherit from StandardToken or, for a token like you would want to
deploy in something like Mist, see HumanStandardToken.sol.
(This implements ONLY the standard functions and NOTHING else.
If you deploy this, you won't have anything useful.)

Implements ERC 20 Token standard: https://github.com/ethereum/EIPs/issues/20
.*/
pragma solidity ^0.4.8;

contract StandardToken is Token {

    using SafeMath for uint;

    function transfer(address _to, uint256 _value) public returns (bool success) {
        //Default assumes totalSupply can't be over max (2^256 - 1).
        //If your token leaves out totalSupply and can issue more tokens as time goes on, you need to check if it doesn't wrap.
        //Replace the if with this one instead.
        //require(balances[msg.sender] >= _value && balances[_to] + _value > balances[_to]);
        require(balances[msg.sender] >= _value);
        balances[msg.sender] = balances[msg.sender].sub(_value);
        balances[_to] = balances[_to].add(_value);
        emit Transfer(msg.sender, _to, _value);
        return true;
    }

    function transferFrom(address _from, address _to, uint256 _value) public returns (bool success) {
        //same as above. Replace this line with the following if you want to protect against wrapping uints.
        //require(balances[_from] >= _value && allowed[_from][msg.sender] >= _value && balances[_to] + _value > balances[_to]);
        require(balances[_from] >= _value && allowed[_from][msg.sender] >= _value);
        balances[_to] = balances[_to].add(_value);
        balances[_from] = balances[_from].sub(_value);
        allowed[_from][msg.sender] = allowed[_from][msg.sender].sub(_value);
        emit Transfer(_from, _to, _value);
        return true;
    }

    function balanceOf(address _owner) public view returns (uint256 balance) {
        return balances[_owner];
    }

    function approve(address _spender, uint256 _value) public returns (bool success) {
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value);
        return true;
    }

    function allowance(address _owner, address _spender) public view returns (uint256 remaining) {
        return allowed[_owner][_spender];
    }

    mapping (address => uint256) balances;
    mapping (address => mapping (address => uint256)) allowed;
}
/*
This Token Contract implements the standard token functionality (https://github.com/ethereum/EIPs/issues/20) as well as the following OPTIONAL extras intended for use by humans.

In other words. This is intended for deployment in something like a Token Factory or Mist wallet, and then used by humans.
Imagine coins, currencies, shares, voting weight, etc.
Machine-based, rapid creation of many tokens would not necessarily need these extra features or will be minted in other manners.

1) Initial Finite Supply (upon creation one specifies how much is minted).
2) In the absence of a token registry: Optional Decimal, Symbol & Name.
3) Optional approveAndCall() functionality to notify a contract if an approval() has occurred.

.*/

pragma solidity ^0.4.8;

contract HumanStandardToken is StandardToken {

    /* Public variables of the token */

    /*
    NOTE:
    The following variables are OPTIONAL vanities. One does not have to include them.
    They allow one to customise the token contract & in no way influences the core functionality.
    Some wallets/interfaces might not even bother to look at this information.
    */
    string public name;                   //fancy name: eg Simon Bucks
    uint8 public decimals;                //How many decimals to show. ie. There could 1000 base units with 3 decimals. Meaning 0.980 SBX = 980 base units. It's like comparing 1 wei to 1 ether.
    string public symbol;                 //An identifier: eg SBX
    string public version = 'H0.1';       //human 0.1 standard. Just an arbitrary versioning scheme.

    constructor (
        uint256 _initialAmount,
        string _tokenName,
        uint8 _decimalUnits,
        string _tokenSymbol
        ) public {
        balances[msg.sender] = _initialAmount;               // Give the creator all initial tokens
        totalSupply = _initialAmount;                        // Update total supply
        name = _tokenName;                                   // Set the name for display purposes
        decimals = _decimalUnits;                            // Amount of decimals for display purposes
        symbol = _tokenSymbol;                               // Set the symbol for display purposes
    }

    /* Approves and then calls the receiving contract */
    function approveAndCall(address _spender, uint256 _value, bytes _extraData) public returns (bool success) {
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value);

        //call the receiveApproval function on the contract you want to be notified. This crafts the function signature manually so one doesn't have to include a contract in here just for this.
        //receiveApproval(address _from, uint256 _value, address _tokenContract, bytes _extraData)
        //it is assumed that when does this that the call *should* succeed, otherwise one would use vanilla approve instead.
        require(_spender.call(bytes4(bytes32(keccak256("receiveApproval(address,uint256,address,bytes)"))), msg.sender, _value, this, _extraData));
        return true;
    }
}

pragma solidity ^0.4.15;

library Set {
    // We define a new struct datatype that will be used to
    // hold its data in the calling contract.
    struct Data { 
        mapping(uint => bool) flags; 
    }

    // Note that the first parameter is of type "storage
    // reference" and thus only its storage address and not
    // its contents is passed as part of the call.  This is a
    // special feature of library functions.  It is idiomatic
    // to call the first parameter 'self', if the function can
    // be seen as a method of that object.
    function insert(Data storage self, uint value) public returns (bool) {
        if (self.flags[value])
            return false; // already there
        self.flags[value] = true;
        return true;
    }

    function remove(Data storage self, uint value) public returns (bool) {
        if (!self.flags[value])
            return false; // not there
        self.flags[value] = false;
        return true;
    }

    function contains(Data storage self, uint value) public view returns (bool) {
        return self.flags[value];
    }
}

pragma solidity ^0.4.19;

// Interface contract to be implemented by DogeToken
contract TransactionProcessor {
    function processTransaction(bytes txn, uint txHash, bytes20 operatorPublicKeyHash, address superblockSubmitterAddress) public returns (uint);
}
// Bitcoin transaction parsing library - modified for DOGE

// Copyright 2016 rain <https://keybase.io/rain>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// https://en.bitcoin.it/wiki/Protocol_documentation#tx
//
// Raw Bitcoin transaction structure:
//
// field     | size | type     | description
// version   | 4    | int32    | transaction version number
// n_tx_in   | 1-9  | var_int  | number of transaction inputs
// tx_in     | 41+  | tx_in[]  | list of transaction inputs
// n_tx_out  | 1-9  | var_int  | number of transaction outputs
// tx_out    | 9+   | tx_out[] | list of transaction outputs
// lock_time | 4    | uint32   | block number / timestamp at which tx locked
//
// Transaction input (tx_in) structure:
//
// field      | size | type     | description
// previous   | 36   | outpoint | Previous output transaction reference
// script_len | 1-9  | var_int  | Length of the signature script
// sig_script | ?    | uchar[]  | Script for confirming transaction authorization
// sequence   | 4    | uint32   | Sender transaction version
//
// OutPoint structure:
//
// field      | size | type     | description
// hash       | 32   | char[32] | The hash of the referenced transaction
// index      | 4    | uint32   | The index of this output in the referenced transaction
//
// Transaction output (tx_out) structure:
//
// field         | size | type     | description
// value         | 8    | int64    | Transaction value (Satoshis)
// pk_script_len | 1-9  | var_int  | Length of the public key script
// pk_script     | ?    | uchar[]  | Public key as a Bitcoin script.
//
// Variable integers (var_int) can be encoded differently depending
// on the represented value, to save space. Variable integers always
// precede an array of a variable length data type (e.g. tx_in).
//
// Variable integer encodings as a function of represented value:
//
// value           | bytes  | format
// <0xFD (253)     | 1      | uint8
// <=0xFFFF (65535)| 3      | 0xFD followed by length as uint16
// <=0xFFFF FFFF   | 5      | 0xFE followed by length as uint32
// -               | 9      | 0xFF followed by length as uint64
//
// Public key scripts `pk_script` are set on the output and can
// take a number of forms. The regular transaction script is
// called 'pay-to-pubkey-hash' (P2PKH):
//
// OP_DUP OP_HASH160 <pubKeyHash> OP_EQUALVERIFY OP_CHECKSIG
//
// OP_x are Bitcoin script opcodes. The bytes representation (including
// the 0x14 20-byte stack push) is:
//
// 0x76 0xA9 0x14 <pubKeyHash> 0x88 0xAC
//
// The <pubKeyHash> is the ripemd160 hash of the sha256 hash of
// the public key, preceded by a network version byte. (21 bytes total)
//
// Network version bytes: 0x00 (mainnet); 0x6f (testnet); 0x34 (namecoin)
//
// The Bitcoin address is derived from the pubKeyHash. The binary form is the
// pubKeyHash, plus a checksum at the end.  The checksum is the first 4 bytes
// of the (32 byte) double sha256 of the pubKeyHash. (25 bytes total)
// This is converted to base58 to form the publicly used Bitcoin address.
// Mainnet P2PKH transaction scripts are to addresses beginning with '1'.
//
// P2SH ('pay to script hash') scripts only supply a script hash. The spender
// must then provide the script that would allow them to redeem this output.
// This allows for arbitrarily complex scripts to be funded using only a
// hash of the script, and moves the onus on providing the script from
// the spender to the redeemer.
//
// The P2SH script format is simple:
//
// OP_HASH160 <scriptHash> OP_EQUAL
//
// 0xA9 0x14 <scriptHash> 0x87
//
// The <scriptHash> is the ripemd160 hash of the sha256 hash of the
// redeem script. The P2SH address is derived from the scriptHash.
// Addresses are the scriptHash with a version prefix of 5, encoded as
// Base58check. These addresses begin with a '3'.

pragma solidity ^0.4.19;

// parse a raw Dogecoin transaction byte array
library DogeMessageLibrary {

    uint constant p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f;  // secp256k1
    uint constant q = (p + 1) / 4;

    // Error codes
    uint constant ERR_INVALID_HEADER = 10050;
    uint constant ERR_COINBASE_INDEX = 10060; // coinbase tx index within Litecoin merkle isn't 0
    uint constant ERR_NOT_MERGE_MINED = 10070; // trying to check AuxPoW on a block that wasn't merge mined
    uint constant ERR_FOUND_TWICE = 10080; // 0xfabe6d6d found twice
    uint constant ERR_NO_MERGE_HEADER = 10090; // 0xfabe6d6d not found
    uint constant ERR_NOT_IN_FIRST_20 = 10100; // chain Merkle root isn't in the first 20 bytes of coinbase tx
    uint constant ERR_CHAIN_MERKLE = 10110;
    uint constant ERR_PARENT_MERKLE = 10120;
    uint constant ERR_PROOF_OF_WORK = 10130;

    enum Network { MAINNET, TESTNET, REGTEST }

    // AuxPoW block fields
    struct AuxPoW {
        uint scryptHash;

        uint txHash;

        uint coinbaseMerkleRoot; // Merkle root of auxiliary block hash tree; stored in coinbase tx field
        uint[] chainMerkleProof; // proves that a given Dogecoin block hash belongs to a tree with the above root
        uint dogeHashIndex; // index of Doge block hash within block hash tree
        uint coinbaseMerkleRootCode; // encodes whether or not the root was found properly

        uint parentMerkleRoot; // Merkle root of transaction tree from parent Litecoin block header
        uint[] parentMerkleProof; // proves that coinbase tx belongs to a tree with the above root
        uint coinbaseTxIndex; // index of coinbase tx within Litecoin tx tree

        uint parentNonce;
    }

    // Dogecoin block header stored as a struct, mostly for readability purposes.
    // BlockHeader structs can be obtained by parsing a block header's first 80 bytes
    // with parseHeaderBytes.
    struct BlockHeader {
        uint32 version;
        uint32 time;
        uint32 bits;
        uint32 nonce;
        uint blockHash;
        uint prevBlock;
        uint merkleRoot;
    }

    // Convert a variable integer into something useful and return it and
    // the index to after it.
    function parseVarInt(bytes txBytes, uint pos) private pure returns (uint, uint) {
        // the first byte tells us how big the integer is
        uint8 ibit = uint8(txBytes[pos]);
        pos += 1;  // skip ibit

        if (ibit < 0xfd) {
            return (ibit, pos);
        } else if (ibit == 0xfd) {
            return (getBytesLE(txBytes, pos, 16), pos + 2);
        } else if (ibit == 0xfe) {
            return (getBytesLE(txBytes, pos, 32), pos + 4);
        } else if (ibit == 0xff) {
            return (getBytesLE(txBytes, pos, 64), pos + 8);
        }
    }
    // convert little endian bytes to uint
    function getBytesLE(bytes data, uint pos, uint bits) internal pure returns (uint) {
        if (bits == 8) {
            return uint8(data[pos]);
        } else if (bits == 16) {
            return uint16(data[pos])
                 + uint16(data[pos + 1]) * 2 ** 8;
        } else if (bits == 32) {
            return uint32(data[pos])
                 + uint32(data[pos + 1]) * 2 ** 8
                 + uint32(data[pos + 2]) * 2 ** 16
                 + uint32(data[pos + 3]) * 2 ** 24;
        } else if (bits == 64) {
            return uint64(data[pos])
                 + uint64(data[pos + 1]) * 2 ** 8
                 + uint64(data[pos + 2]) * 2 ** 16
                 + uint64(data[pos + 3]) * 2 ** 24
                 + uint64(data[pos + 4]) * 2 ** 32
                 + uint64(data[pos + 5]) * 2 ** 40
                 + uint64(data[pos + 6]) * 2 ** 48
                 + uint64(data[pos + 7]) * 2 ** 56;
        }
    }

    struct ParseTransactionVariablesStruct {
        uint pos;
        bytes20 output_public_key_hash;
        uint output_value;
        uint16 outputIndex;
        bytes32 inputPubKey;
        bool inputPubKeyOdd;
    }

    // @dev - Parses a doge tx
    //
    // @param txBytes - tx byte array
    // @param expected_output_public_key_hash - lock address (actually, it's public key hash expected to be on 1st or 2nd output, require() fails otherwise)
    // Outputs
    // @return output_value - amount sent to the lock address in satoshis
    // @return inputPubKey - "x" axis value of the public key used to sign the first output
    // @return inputPubKeyOdd - Indicates inputPubKey odd bit
    // @return outputIndex - number of output where expected_output_address was found

    function parseTransaction(bytes txBytes, bytes20 expected_output_public_key_hash) internal view
             returns (uint, bytes20, address, uint16)
    {
        ParseTransactionVariablesStruct memory variables;
        uint[] memory input_script_lens;
        uint[] memory input_script_starts;

        variables.pos = 4;  // skip version
        (input_script_starts, input_script_lens, variables.pos) = scanInputs(txBytes, variables.pos, 0);

        (variables.inputPubKey, variables.inputPubKeyOdd) = getInputPubKey(txBytes, input_script_starts[0]);

        bytes20 firstInputPublicKeyHash = pub2PubKeyHash(variables.inputPubKey, variables.inputPubKeyOdd);
        address firstInputEthAddress;

        uint operator_value;
        uint16 operator_index;
        (variables.output_public_key_hash, operator_value, operator_index, firstInputEthAddress) = findOperatorOutput(expected_output_public_key_hash, txBytes, variables.pos);

        require(variables.output_public_key_hash == expected_output_public_key_hash ||
            firstInputPublicKeyHash == expected_output_public_key_hash);
        // The output we are looking for should be the first or the second output
        if (variables.output_public_key_hash == expected_output_public_key_hash) {
            variables.output_value = operator_value;
            variables.outputIndex = operator_index;
        }
        // If no embedded ethereum address use address derived from first input public
        if (firstInputEthAddress == address(0x0)) {
            firstInputEthAddress = pub2address(uint(variables.inputPubKey), variables.inputPubKeyOdd);
        }
        return (variables.output_value, firstInputPublicKeyHash, firstInputEthAddress, variables.outputIndex);
    }

    // Search output public key hash and embedded ethereum address in transaction outputs at txBytes
    // Returns output amount, index and ethereum address
    function findOperatorOutput(bytes20 expected_output_public_key_hash, bytes memory txBytes, uint pos)
             private pure returns (bytes20, uint, uint16, address) {
        uint[] memory output_script_lens;
        uint[] memory output_script_starts;
        uint[] memory output_values;
        (output_values, output_script_starts, output_script_lens, pos) = scanOutputs(txBytes, pos, 3);

        bytes20 output_public_key_hash;
        uint operator_index = output_script_starts.length;
        address eth_address;
        for (uint i=0; i<output_script_starts.length; ++i) {
            output_public_key_hash = parseP2PKHOutputScript(txBytes, output_script_starts[i], output_script_lens[i]);
            if (expected_output_public_key_hash == output_public_key_hash) {
                operator_index = i;
            }
            if (isEthereumAddress(txBytes, output_script_starts[i], output_script_lens[i])) {
                eth_address = readEthereumAddress(txBytes, output_script_starts[i], output_script_lens[i]);
            }
        }
        if (operator_index < output_script_starts.length) {
            return (expected_output_public_key_hash, output_values[operator_index], uint16(operator_index), eth_address);
        }
        // No operator output, it might be an unlock operation
        return (bytes20(0x0), 0, 0, address(0x0));
    }

    // scan the full transaction bytes and return the first two output
    // values (in satoshis) and addresses (in binary)
    function getFirstTwoOutputs(bytes txBytes) internal pure
             returns (uint, bytes20, uint, bytes20)
    {
        uint pos;
        uint[] memory input_script_lens;
        uint[] memory output_script_lens;
        uint[] memory script_starts;
        uint[] memory output_values;
        bytes20[] memory output_public_key_hashes = new bytes20[](2);

        pos = 4;  // skip version

        (, input_script_lens, pos) = scanInputs(txBytes, pos, 0);

        (output_values, script_starts, output_script_lens, pos) = scanOutputs(txBytes, pos, 2);

        for (uint i = 0; i < 2; i++) {
            bytes20 pkhash = parseP2PKHOutputScript(txBytes, script_starts[i], output_script_lens[i]);
            output_public_key_hashes[i] = pkhash;
        }

        return (output_values[0], output_public_key_hashes[0],
                output_values[1], output_public_key_hashes[1]);
    }

    function getFirstInputPubKey(bytes txBytes) private pure
             returns (bytes32, bool)
    {
        uint pos;

        pos = 4;  // skip version

        (, pos) = parseVarInt(txBytes, pos);
        return getInputPubKey(txBytes, pos);
    }

    function getInputPubKey(bytes txBytes, uint pos) private pure
             returns (bytes32, bool)
    {
        pos += 36;  // skip outpoint
        (, pos) = parseVarInt(txBytes, pos);
        bytes32 pubKey;
        bool odd;
        (, pubKey, odd, pos) = parseScriptSig(txBytes, pos);
        return (pubKey, odd);
    }

    // Check whether `btcAddress` is in the transaction outputs *and*
    // whether *at least* `value` has been sent to it.
    function checkValueSent(bytes txBytes, bytes20 btcAddress, uint value) private pure
             returns (bool)
    {
        uint pos = 4;  // skip version
        (,, pos) = scanInputs(txBytes, pos, 0);  // find end of inputs

        // scan *all* the outputs and find where they are
        uint[] memory output_values;
        uint[] memory script_starts;
        uint[] memory output_script_lens;
        (output_values, script_starts, output_script_lens,) = scanOutputs(txBytes, pos, 0);

        // look at each output and check whether it at least value to btcAddress
        for (uint i = 0; i < output_values.length; i++) {
            bytes20 pkhash = parseOutputScript(txBytes, script_starts[i], output_script_lens[i]);
            if (pkhash == btcAddress && output_values[i] >= value) {
                return true;
            }
        }
    }
    // scan the inputs and find the script lengths.
    // return an array of script lengths and the end position
    // of the inputs.
    // takes a 'stop' argument which sets the maximum number of
    // outputs to scan through. stop=0 => scan all.
    function scanInputs(bytes txBytes, uint pos, uint stop) private pure
             returns (uint[], uint[], uint)
    {
        uint n_inputs;
        uint halt;
        uint script_len;

        (n_inputs, pos) = parseVarInt(txBytes, pos);

        if (stop == 0 || stop > n_inputs) {
            halt = n_inputs;
        } else {
            halt = stop;
        }

        uint[] memory script_starts = new uint[](halt);
        uint[] memory script_lens = new uint[](halt);

        for (uint256 i = 0; i < halt; i++) {
            script_starts[i] = pos;
            pos += 36;  // skip outpoint
            (script_len, pos) = parseVarInt(txBytes, pos);
            script_lens[i] = script_len;
            pos += script_len + 4;  // skip sig_script, seq
        }

        return (script_starts, script_lens, pos);
    }
    // similar to scanInputs, but consumes less gas since it doesn't store the inputs
    // also returns position of coinbase tx for later use
    function skipInputsAndGetScriptPos(bytes txBytes, uint pos, uint stop) private pure
             returns (uint, uint)
    {
        uint script_pos;

        uint n_inputs;
        uint halt;
        uint script_len;

        (n_inputs, pos) = parseVarInt(txBytes, pos);

        if (stop == 0 || stop > n_inputs) {
            halt = n_inputs;
        } else {
            halt = stop;
        }

        for (uint256 i = 0; i < halt; i++) {
            pos += 36;  // skip outpoint
            (script_len, pos) = parseVarInt(txBytes, pos);
            if (i == 0)
                script_pos = pos; // first input script begins where first script length ends
            // (script_len, pos) = (1, 0);
            pos += script_len + 4;  // skip sig_script, seq
        }

        return (pos, script_pos);
    }
    // scan the outputs and find the values and script lengths.
    // return array of values, array of script lengths and the
    // end position of the outputs.
    // takes a 'stop' argument which sets the maximum number of
    // outputs to scan through. stop=0 => scan all.
    function scanOutputs(bytes txBytes, uint pos, uint stop) private pure
             returns (uint[], uint[], uint[], uint)
    {
        uint n_outputs;
        uint halt;
        uint script_len;

        (n_outputs, pos) = parseVarInt(txBytes, pos);

        if (stop == 0 || stop > n_outputs) {
            halt = n_outputs;
        } else {
            halt = stop;
        }

        uint[] memory script_starts = new uint[](halt);
        uint[] memory script_lens = new uint[](halt);
        uint[] memory output_values = new uint[](halt);

        for (uint256 i = 0; i < halt; i++) {
            output_values[i] = getBytesLE(txBytes, pos, 64);
            pos += 8;

            (script_len, pos) = parseVarInt(txBytes, pos);
            script_starts[i] = pos;
            script_lens[i] = script_len;
            pos += script_len;
        }

        return (output_values, script_starts, script_lens, pos);
    }
    // similar to scanOutputs, but consumes less gas since it doesn't store the outputs
    function skipOutputs(bytes txBytes, uint pos, uint stop) private pure
             returns (uint)
    {
        uint n_outputs;
        uint halt;
        uint script_len;

        (n_outputs, pos) = parseVarInt(txBytes, pos);

        if (stop == 0 || stop > n_outputs) {
            halt = n_outputs;
        } else {
            halt = stop;
        }

        for (uint256 i = 0; i < halt; i++) {
            pos += 8;

            (script_len, pos) = parseVarInt(txBytes, pos);
            pos += script_len;
        }

        return pos;
    }
    // get final position of inputs, outputs and lock time
    // this is a helper function to slice a byte array and hash the inputs, outputs and lock time
    function getSlicePosAndScriptPos(bytes txBytes, uint pos) private pure
             returns (uint slicePos, uint scriptPos)
    {
        (slicePos, scriptPos) = skipInputsAndGetScriptPos(txBytes, pos + 4, 0);
        slicePos = skipOutputs(txBytes, slicePos, 0);
        slicePos += 4; // skip lock time
    }
    // scan a Merkle branch.
    // return array of values and the end position of the sibling hashes.
    // takes a 'stop' argument which sets the maximum number of
    // siblings to scan through. stop=0 => scan all.
    function scanMerkleBranch(bytes txBytes, uint pos, uint stop) private pure
             returns (uint[], uint)
    {
        uint n_siblings;
        uint halt;

        (n_siblings, pos) = parseVarInt(txBytes, pos);

        if (stop == 0 || stop > n_siblings) {
            halt = n_siblings;
        } else {
            halt = stop;
        }

        uint[] memory sibling_values = new uint[](halt);

        for (uint256 i = 0; i < halt; i++) {
            sibling_values[i] = flip32Bytes(sliceBytes32Int(txBytes, pos));
            pos += 32;
        }

        return (sibling_values, pos);
    }
    // Slice 20 contiguous bytes from bytes `data`, starting at `start`
    function sliceBytes20(bytes data, uint start) private pure returns (bytes20) {
        uint160 slice = 0;
        // FIXME: With solc v0.4.24 and optimizations enabled
        // using uint160 for index i will generate an error
        // "Error: VM Exception while processing transaction: Error: redPow(normalNum)"
        for (uint256 i = 0; i < 20; i++) {
            slice += uint160(data[i + start]) << (8 * (19 - i));
        }
        return bytes20(slice);
    }
    // Slice 32 contiguous bytes from bytes `data`, starting at `start`
    function sliceBytes32Int(bytes data, uint start) private pure returns (uint slice) {
        for (uint i = 0; i < 32; i++) {
            if (i + start < data.length) {
                slice += uint(data[i + start]) << (8 * (31 - i));
            }
        }
    }

    // @dev returns a portion of a given byte array specified by its starting and ending points
    // Should be private, made internal for testing
    // Breaks underscore naming convention for parameters because it raises a compiler error
    // if `offset` is changed to `_offset`.
    //
    // @param _rawBytes - array to be sliced
    // @param offset - first byte of sliced array
    // @param _endIndex - last byte of sliced array
    function sliceArray(bytes memory _rawBytes, uint offset, uint _endIndex) internal view returns (bytes) {
        uint len = _endIndex - offset;
        bytes memory result = new bytes(len);
        assembly {
            // Call precompiled contract to copy data
            if iszero(staticcall(gas, 0x04, add(add(_rawBytes, 0x20), offset), len, add(result, 0x20), len)) {
                revert(0, 0)
            }
        }
        return result;
    }
    // returns true if the bytes located in txBytes by pos and
    // script_len represent a P2PKH script
    function isP2PKH(bytes txBytes, uint pos, uint script_len) private pure returns (bool) {
        return (script_len == 25)           // 20 byte pubkeyhash + 5 bytes of script
            && (txBytes[pos] == 0x76)       // OP_DUP
            && (txBytes[pos + 1] == 0xa9)   // OP_HASH160
            && (txBytes[pos + 2] == 0x14)   // bytes to push
            && (txBytes[pos + 23] == 0x88)  // OP_EQUALVERIFY
            && (txBytes[pos + 24] == 0xac); // OP_CHECKSIG
    }
    // returns true if the bytes located in txBytes by pos and
    // script_len represent a P2SH script
    function isP2SH(bytes txBytes, uint pos, uint script_len) private pure returns (bool) {
        return (script_len == 23)           // 20 byte scripthash + 3 bytes of script
            && (txBytes[pos + 0] == 0xa9)   // OP_HASH160
            && (txBytes[pos + 1] == 0x14)   // bytes to push
            && (txBytes[pos + 22] == 0x87); // OP_EQUAL
    }
    // Get the pubkeyhash / scripthash from an output script. Assumes
    // pay-to-pubkey-hash (P2PKH) or pay-to-script-hash (P2SH) outputs.
    // Returns the pubkeyhash/ scripthash, or zero if unknown output.
    function parseOutputScript(bytes txBytes, uint pos, uint script_len) private pure
             returns (bytes20)
    {
        if (isP2PKH(txBytes, pos, script_len)) {
            return sliceBytes20(txBytes, pos + 3);
        } else if (isP2SH(txBytes, pos, script_len)) {
            return sliceBytes20(txBytes, pos + 2);
        } else {
            return;
        }
    }

    // Get the pubkeyhash from an output script. Assumes
    // pay-to-pubkey-hash (P2PKH) outputs.
    // Returns the pubkeyhash, or zero if unknown output.
    function parseP2PKHOutputScript(bytes txBytes, uint pos, uint script_len) private pure
             returns (bytes20)
    {
        if (isP2PKH(txBytes, pos, script_len)) {
            return sliceBytes20(txBytes, pos + 3);
        } else {
            return;
        }
    }


    // Parse a P2PKH scriptSig
    function parseScriptSig(bytes txBytes, uint pos) private pure
             returns (bytes, bytes32, bool, uint)
    {
        bytes memory sig;
        bytes32 pubKey;
        bool odd;
        (sig, pos) = parseSignature(txBytes, pos);
        (pubKey, odd, pos) = parsePubKey(txBytes, pos);
        return (sig, pubKey, odd, pos);
    }

    // Extract a signature
    function parseSignature(bytes txBytes, uint pos) private pure
             returns (bytes, uint)
    {
        uint8 op;
        bytes memory sig;
        (op, pos) = getOpcode(txBytes, pos);
        require(op >= 9 && op <= 73);
        require(uint8(txBytes[pos]) == 0x30);
        //FIXME: Copy signature
        pos += op;
        return (sig, pos);
    }

    // Extract public key
    function parsePubKey(bytes txBytes, uint pos) private pure
             returns (bytes32, bool, uint)
    {
        uint8 op;
        (op, pos) = getOpcode(txBytes, pos);
        //FIXME: Add support for uncompressed public keys
        require(op == 33);
        bytes32 pubKey;
        bool odd = txBytes[pos] == 0x03;
        pos += 1;
        assembly {
            pubKey := mload(add(add(txBytes, 0x20), pos))
        }
        pos += 32;
        return (pubKey, odd, pos);
    }

    // Returns true if the tx output is an embedded ethereum address
    function isEthereumAddress(bytes txBytes, uint pos, uint len) private pure
             returns (bool) {
        // scriptPub format is
        // 0x6a OP_RETURN
        // 0x14 PUSH20
        // []   20 bytes of the ethereum address
        return len == 20+2 &&
            txBytes[pos] == byte(0x6a) &&
            txBytes[pos+1] == byte(20);
    }

    // Read the ethereum address embedded in the tx output
    function readEthereumAddress(bytes txBytes, uint pos, uint) private pure
             returns (address) {
        uint256 data;
        assembly {
            data := mload(add(add(txBytes, 22), pos))
        }
        return address(uint160(data));
    }

    // Read next opcode from script
    function getOpcode(bytes txBytes, uint pos) private pure
             returns (uint8, uint)
    {
        return (uint8(txBytes[pos]), pos + 1);
    }

    function expmod(uint256 base, uint256 e, uint256 m) internal view returns (uint256 o) {
        assembly {
            // pointer to free memory
            let p := mload(0x40)
            mstore(p, 0x20)             // Length of Base
            mstore(add(p, 0x20), 0x20)  // Length of Exponent
            mstore(add(p, 0x40), 0x20)  // Length of Modulus
            mstore(add(p, 0x60), base)  // Base
            mstore(add(p, 0x80), e)     // Exponent
            mstore(add(p, 0xa0), m)     // Modulus
            // call modexp precompile!
            if iszero(staticcall(gas, 0x05, p, 0xc0, p, 0x20)) {
                revert(0, 0)
            }
            // data
            o := mload(p)
        }
    }

    function pub2address(uint x, bool odd) internal view returns (address) {
        // First, uncompress pub key
        uint yy = mulmod(x, x, p);
        yy = mulmod(yy, x, p);
        yy = addmod(yy, 7, p);
        uint y = expmod(yy, q, p);
        if (((y & 1) == 1) != odd) {
          y = p - y;
        }
        require(yy == mulmod(y, y, p));
        // Now, with uncompressed x and y, create the address
        return address(keccak256(abi.encodePacked(x, y)));
    }

    // Gets the public key hash given a public key
    function pub2PubKeyHash(bytes32 pub, bool odd) internal pure returns (bytes20) {
        byte firstByte = odd ? byte(0x03) : byte(0x02);
        return ripemd160(abi.encodePacked(sha256(abi.encodePacked(firstByte, pub))));
    }

    // @dev - convert an unsigned integer from little-endian to big-endian representation
    //
    // @param _input - little-endian value
    // @return - input value in big-endian format
    function flip32Bytes(uint _input) internal pure returns (uint result) {
        assembly {
            let pos := mload(0x40)
            for { let i := 0 } lt(i, 32) { i := add(i, 1) } {
                mstore8(add(pos, i), byte(sub(31, i), _input))
            }
            result := mload(pos)
        }
    }
    // helpers for flip32Bytes
    struct UintWrapper {
        uint value;
    }

    function ptr(UintWrapper memory uw) private pure returns (uint addr) {
        assembly {
            addr := uw
        }
    }

    function parseAuxPoW(bytes rawBytes, uint pos, uint len) internal view
             returns (AuxPoW memory auxpow)
    {
        // we need to traverse the bytes with a pointer because some fields are of variable length
        pos += 80; // skip non-AuxPoW header
        // auxpow.firstBytes = sliceBytes32Int(rawBytes, pos);
        uint slicePos;
        uint inputScriptPos;
        (slicePos, inputScriptPos) = getSlicePosAndScriptPos(rawBytes, pos);
        auxpow.txHash = dblShaFlipMem(rawBytes, pos, slicePos - pos);
        pos = slicePos;
        auxpow.scryptHash = sliceBytes32Int(rawBytes, pos);
        pos += 32;
        (auxpow.parentMerkleProof, pos) = scanMerkleBranch(rawBytes, pos, 0);
        auxpow.coinbaseTxIndex = getBytesLE(rawBytes, pos, 32);
        pos += 4;
        (auxpow.chainMerkleProof, pos) = scanMerkleBranch(rawBytes, pos, 0);
        auxpow.dogeHashIndex = getBytesLE(rawBytes, pos, 32);
        pos += 40; // skip hash that was just read, parent version and prev block
        auxpow.parentMerkleRoot = sliceBytes32Int(rawBytes, pos);
        pos += 40; // skip root that was just read, parent block timestamp and bits
        auxpow.parentNonce = getBytesLE(rawBytes, pos, 32);
        uint coinbaseMerkleRootPosition;
        (auxpow.coinbaseMerkleRoot, coinbaseMerkleRootPosition, auxpow.coinbaseMerkleRootCode) = findCoinbaseMerkleRoot(rawBytes);
        if (coinbaseMerkleRootPosition - inputScriptPos > 20 && auxpow.coinbaseMerkleRootCode == 1) {
            // if it was found once and only once but not in the first 20 bytes, return this error code
            auxpow.coinbaseMerkleRootCode = ERR_NOT_IN_FIRST_20;
        }
    }

    // @dev - looks for {0xfa, 0xbe, 'm', 'm'} byte sequence
    // returns the following 32 bytes if it appears once and only once,
    // 0 otherwise
    // also returns the position where the bytes first appear
    function findCoinbaseMerkleRoot(bytes rawBytes) private pure
             returns (uint, uint, uint)
    {
        uint position;
        bool found = false;

        for (uint i = 0; i < rawBytes.length; ++i) {
            if (rawBytes[i] == 0xfa && rawBytes[i+1] == 0xbe && rawBytes[i+2] == 0x6d && rawBytes[i+3] == 0x6d) {
                if (found) { // found twice
                    return (0, position - 4, ERR_FOUND_TWICE);
                } else {
                    found = true;
                    position = i + 4;
                }
            }
        }

        if (!found) { // no merge mining header
            return (0, position - 4, ERR_NO_MERGE_HEADER);
        } else {
            return (sliceBytes32Int(rawBytes, position), position - 4, 1);
        }
    }

    // @dev - Evaluate the merkle root
    //
    // Given an array of hashes it calculates the
    // root of the merkle tree.
    //
    // @return root of merkle tree
    function makeMerkle(bytes32[] hashes2) external pure returns (bytes32) {
        bytes32[] memory hashes = hashes2;
        uint length = hashes.length;
        if (length == 1) return hashes[0];
        require(length > 0);
        uint i;
        uint j;
        uint k;
        k = 0;
        while (length > 1) {
            k = 0;
            for (i = 0; i < length; i += 2) {
                j = i+1<length ? i+1 : length-1;
                hashes[k] = bytes32(concatHash(uint(hashes[i]), uint(hashes[j])));
                k += 1;
            }
            length = k;
        }
        return hashes[0];
    }

    // @dev - For a valid proof, returns the root of the Merkle tree.
    //
    // @param _txHash - transaction hash
    // @param _txIndex - transaction's index within the block it's assumed to be in
    // @param _siblings - transaction's Merkle siblings
    // @return - Merkle tree root of the block the transaction belongs to if the proof is valid,
    // garbage if it's invalid
    function computeMerkle(uint _txHash, uint _txIndex, uint[] _siblings) internal pure returns (uint) {
        uint resultHash = _txHash;
        uint i = 0;
        while (i < _siblings.length) {
            uint proofHex = _siblings[i];

            uint sideOfSiblings = _txIndex % 2;  // 0 means _siblings is on the right; 1 means left

            uint left;
            uint right;
            if (sideOfSiblings == 1) {
                left = proofHex;
                right = resultHash;
            } else if (sideOfSiblings == 0) {
                left = resultHash;
                right = proofHex;
            }

            resultHash = concatHash(left, right);

            _txIndex /= 2;
            i += 1;
        }

        return resultHash;
    }

    // @dev - calculates the Merkle root of a tree containing Litecoin transactions
    // in order to prove that `ap`'s coinbase tx is in that Litecoin block.
    //
    // @param _ap - AuxPoW information
    // @return - Merkle root of Litecoin block that the Dogecoin block
    // with this info was mined in if AuxPoW Merkle proof is correct,
    // garbage otherwise
    function computeParentMerkle(AuxPoW _ap) internal pure returns (uint) {
        return flip32Bytes(computeMerkle(_ap.txHash,
                                         _ap.coinbaseTxIndex,
                                         _ap.parentMerkleProof));
    }

    // @dev - calculates the Merkle root of a tree containing auxiliary block hashes
    // in order to prove that the Dogecoin block identified by _blockHash
    // was merge-mined in a Litecoin block.
    //
    // @param _blockHash - SHA-256 hash of a certain Dogecoin block
    // @param _ap - AuxPoW information corresponding to said block
    // @return - Merkle root of auxiliary chain tree
    // if AuxPoW Merkle proof is correct, garbage otherwise
    function computeChainMerkle(uint _blockHash, AuxPoW _ap) internal pure returns (uint) {
        return computeMerkle(_blockHash,
                             _ap.dogeHashIndex,
                             _ap.chainMerkleProof);
    }

    // @dev - Helper function for Merkle root calculation.
    // Given two sibling nodes in a Merkle tree, calculate their parent.
    // Concatenates hashes `_tx1` and `_tx2`, then hashes the result.
    //
    // @param _tx1 - Merkle node (either root or internal node)
    // @param _tx2 - Merkle node (either root or internal node), has to be `_tx1`'s sibling
    // @return - `_tx1` and `_tx2`'s parent, i.e. the result of concatenating them,
    // hashing that twice and flipping the bytes.
    function concatHash(uint _tx1, uint _tx2) internal pure returns (uint) {
        return flip32Bytes(uint(sha256(abi.encodePacked(sha256(abi.encodePacked(flip32Bytes(_tx1), flip32Bytes(_tx2)))))));
    }

    // @dev - checks if a merge-mined block's Merkle proofs are correct,
    // i.e. Doge block hash is in coinbase Merkle tree
    // and coinbase transaction is in parent Merkle tree.
    //
    // @param _blockHash - SHA-256 hash of the block whose Merkle proofs are being checked
    // @param _ap - AuxPoW struct corresponding to the block
    // @return 1 if block was merge-mined and coinbase index, chain Merkle root and Merkle proofs are correct,
    // respective error code otherwise
    function checkAuxPoW(uint _blockHash, AuxPoW _ap) internal pure returns (uint) {
        if (_ap.coinbaseTxIndex != 0) {
            return ERR_COINBASE_INDEX;
        }

        if (_ap.coinbaseMerkleRootCode != 1) {
            return _ap.coinbaseMerkleRootCode;
        }

        if (computeChainMerkle(_blockHash, _ap) != _ap.coinbaseMerkleRoot) {
            return ERR_CHAIN_MERKLE;
        }

        if (computeParentMerkle(_ap) != _ap.parentMerkleRoot) {
            return ERR_PARENT_MERKLE;
        }

        return 1;
    }

    function sha256mem(bytes memory _rawBytes, uint offset, uint len) internal view returns (bytes32 result) {
        assembly {
            // Call sha256 precompiled contract (located in address 0x02) to copy data.
            // Assign to ptr the next available memory position (stored in memory position 0x40).
            let ptr := mload(0x40)
            if iszero(staticcall(gas, 0x02, add(add(_rawBytes, 0x20), offset), len, ptr, 0x20)) {
                revert(0, 0)
            }
            result := mload(ptr)
        }
    }

    // @dev - Bitcoin-way of hashing
    // @param _dataBytes - raw data to be hashed
    // @return - result of applying SHA-256 twice to raw data and then flipping the bytes
    function dblShaFlip(bytes _dataBytes) internal pure returns (uint) {
        return flip32Bytes(uint(sha256(abi.encodePacked(sha256(abi.encodePacked(_dataBytes))))));
    }

    // @dev - Bitcoin-way of hashing
    // @param _dataBytes - raw data to be hashed
    // @return - result of applying SHA-256 twice to raw data and then flipping the bytes
    function dblShaFlipMem(bytes memory _rawBytes, uint offset, uint len) internal view returns (uint) {
        return flip32Bytes(uint(sha256(abi.encodePacked(sha256mem(_rawBytes, offset, len)))));
    }

    // @dev – Read a bytes32 from an offset in the byte array
    function readBytes32(bytes data, uint offset) internal pure returns (bytes32) {
        bytes32 result;
        assembly {
            result := mload(add(add(data, 0x20), offset))
        }
        return result;
    }

    // @dev – Read an uint32 from an offset in the byte array
    function readUint32(bytes data, uint offset) internal pure returns (uint32) {
        uint32 result;
        assembly {
            let word := mload(add(add(data, 0x20), offset))
            result := add(byte(3, word),
                add(mul(byte(2, word), 0x100),
                    add(mul(byte(1, word), 0x10000),
                        mul(byte(0, word), 0x1000000))))
        }
        return result;
    }

    // @dev - Bitcoin-way of computing the target from the 'bits' field of a block header
    // based on http://www.righto.com/2014/02/bitcoin-mining-hard-way-algorithms.html//ref3
    //
    // @param _bits - difficulty in bits format
    // @return - difficulty in target format
    function targetFromBits(uint32 _bits) internal pure returns (uint) {
        uint exp = _bits / 0x1000000;  // 2**24
        uint mant = _bits & 0xffffff;
        return mant * 256**(exp - 3);
    }

    uint constant DOGECOIN_DIFFICULTY_ONE = 0xFFFFF * 256**(0x1e - 3);

    // @dev - Calculate dogecoin difficulty from target
    // https://en.bitcoin.it/wiki/Difficulty
    // Min difficulty for bitcoin is 0x1d00ffff
    // Min difficulty for dogecoin is 0x1e0fffff
    function targetToDiff(uint target) internal pure returns (uint) {
        return DOGECOIN_DIFFICULTY_ONE / target;
    }

    // @dev - Parse an array of bytes32
    function parseBytes32Array(bytes data) external pure returns (bytes32[]) {
        require(data.length % 32 == 0);
        uint count = data.length / 32;
        bytes32[] memory hashes = new bytes32[](count);
        for (uint i=0; i<count; ++i) {
            hashes[i] = readBytes32(data, 32*i);
        }
        return hashes;
    }

    // 0x00 version
    // 0x04 prev block hash
    // 0x24 merkle root
    // 0x44 timestamp
    // 0x48 bits
    // 0x4c nonce

    // @dev - extract version field from a raw Dogecoin block header
    //
    // @param _blockHeader - Dogecoin block header bytes
    // @param pos - where to start reading version from
    // @return - block's version in big endian format
    function getVersion(bytes memory _blockHeader, uint pos) internal pure returns (uint32 version) {
        assembly {
            let word := mload(add(add(_blockHeader, 0x4), pos))
            version := add(byte(24, word),
                add(mul(byte(25, word), 0x100),
                    add(mul(byte(26, word), 0x10000),
                        mul(byte(27, word), 0x1000000))))
        }
    }

    // @dev - extract previous block field from a raw Dogecoin block header
    //
    // @param _blockHeader - Dogecoin block header bytes
    // @param pos - where to start reading hash from
    // @return - hash of block's parent in big endian format
    function getHashPrevBlock(bytes memory _blockHeader, uint pos) internal pure returns (uint) {
        uint hashPrevBlock;
        assembly {
            hashPrevBlock := mload(add(add(_blockHeader, 0x24), pos))
        }
        return flip32Bytes(hashPrevBlock);
    }

    // @dev - extract Merkle root field from a raw Dogecoin block header
    //
    // @param _blockHeader - Dogecoin block header bytes
    // @param pos - where to start reading root from
    // @return - block's Merkle root in big endian format
    function getHeaderMerkleRoot(bytes _blockHeader, uint pos) public pure returns (uint) {
        uint merkle;
        assembly {
            merkle := mload(add(add(_blockHeader, 0x44), pos))
        }
        return flip32Bytes(merkle);
    }

    // @dev - extract bits field from a raw Dogecoin block header
    //
    // @param _blockHeader - Dogecoin block header bytes
    // @param pos - where to start reading bits from
    // @return - block's difficulty in bits format, also big-endian
    function getBits(bytes memory _blockHeader, uint pos) internal pure returns (uint32 bits) {
        assembly {
            let word := mload(add(add(_blockHeader, 0x50), pos))
            bits := add(byte(24, word),
                add(mul(byte(25, word), 0x100),
                    add(mul(byte(26, word), 0x10000),
                        mul(byte(27, word), 0x1000000))))
        }
    }

    // @dev - extract timestamp field from a raw Dogecoin block header
    //
    // @param _blockHeader - Dogecoin block header bytes
    // @param pos - where to start reading bits from
    // @return - block's timestamp in big-endian format
    function getTimestamp(bytes memory _blockHeader, uint pos) internal pure returns (uint32 time) {
        assembly {
            let word := mload(add(add(_blockHeader, 0x4c), pos))
            time := add(byte(24, word),
                add(mul(byte(25, word), 0x100),
                    add(mul(byte(26, word), 0x10000),
                        mul(byte(27, word), 0x1000000))))
        }
    }

    // @dev - converts raw bytes representation of a Dogecoin block header to struct representation
    //
    // @param _rawBytes - first 80 bytes of a block header
    // @return - exact same header information in BlockHeader struct form
    function parseHeaderBytes(bytes _rawBytes, uint pos) internal view returns (BlockHeader bh) {
        bh.version = getVersion(_rawBytes, pos);
        bh.time = getTimestamp(_rawBytes, pos);
        bh.bits = getBits(_rawBytes, pos);
        bh.blockHash = dblShaFlipMem(_rawBytes, pos, 80);
        bh.prevBlock = getHashPrevBlock(_rawBytes, pos);
        bh.merkleRoot = getHeaderMerkleRoot(_rawBytes, pos);
    }

    uint32 constant VERSION_AUXPOW = (1 << 8);

    // @dev - Converts a bytes of size 4 to uint32,
    // e.g. for input [0x01, 0x02, 0x03 0x04] returns 0x01020304
    function bytesToUint32Flipped(bytes input, uint pos) internal pure returns (uint32 result) {
        result = uint32(input[pos]) + uint32(input[pos + 1])*(2**8) + uint32(input[pos + 2])*(2**16) + uint32(input[pos + 3])*(2**24);
    }

    // @dev - checks version to determine if a block has merge mining information
    function isMergeMined(bytes _rawBytes, uint pos) internal pure returns (bool) {
        return bytesToUint32Flipped(_rawBytes, pos) & VERSION_AUXPOW != 0;
    }

    // @dev - checks version to determine if a block has merge mining information
    function isMergeMined(BlockHeader _blockHeader) internal pure returns (bool) {
        return _blockHeader.version & VERSION_AUXPOW != 0;
    }

    // @dev - Verify block header
    // @param _blockHeaderBytes - array of bytes with the block header
    // @param _pos - starting position of the block header
    // @param _len - length of the block header
    // @param _proposedBlockScryptHash - proposed block scrypt hash
    // @return - [ErrorCode, BlockSha256Hash, BlockScryptHash, IsMergeMined]
    function verifyBlockHeader(bytes _blockHeaderBytes, uint _pos, uint _len, uint _proposedBlockScryptHash) external view returns (uint, uint, uint, bool) {
        BlockHeader memory blockHeader = parseHeaderBytes(_blockHeaderBytes, _pos);
        uint blockSha256Hash = blockHeader.blockHash;
        if (isMergeMined(blockHeader)) {
            AuxPoW memory ap = parseAuxPoW(_blockHeaderBytes, _pos, _len);
            if (flip32Bytes(ap.scryptHash) > targetFromBits(blockHeader.bits)) {
                return (ERR_PROOF_OF_WORK, blockHeader.blockHash, ap.scryptHash, true);
            }
            uint auxPoWCode = checkAuxPoW(blockSha256Hash, ap);
            if (auxPoWCode != 1) {
                return (auxPoWCode, blockHeader.blockHash, ap.scryptHash, true);
            }
            return (0, blockHeader.blockHash, ap.scryptHash, true);
        } else {
            if (flip32Bytes(_proposedBlockScryptHash) > targetFromBits(blockHeader.bits)) {
                return (ERR_PROOF_OF_WORK, blockHeader.blockHash, _proposedBlockScryptHash, false);
            }
            return (0, blockHeader.blockHash, _proposedBlockScryptHash, false);
        }
    }

    // @dev - Calculate difficulty from compact representation (bits) found in block
    function diffFromBits(uint32 bits) external pure returns (uint) {
        return targetToDiff(targetFromBits(bits));
    }

    // For verifying Dogecoin difficulty
    uint constant DIFFICULTY_ADJUSTMENT_INTERVAL = 1;  // Bitcoin adjusts every block
    uint constant TARGET_TIMESPAN =  60;  // 1 minute
    uint constant TARGET_TIMESPAN_DIV_4 = TARGET_TIMESPAN / 4;
    uint constant TARGET_TIMESPAN_MUL_4 = TARGET_TIMESPAN * 4;
    uint constant UNROUNDED_MAX_TARGET = 2**224 - 1;  // different from (2**16-1)*2**208 http =//bitcoin.stackexchange.com/questions/13803/how/ exactly-was-the-original-coefficient-for-difficulty-determined
    uint constant POW_LIMIT = 0x00000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;

    // @dev - Implementation of DigiShield, almost directly translated from
    // C++ implementation of Dogecoin. See function calculateDogecoinNextWorkRequired
    // on dogecoin/src/dogecoin.cpp for more details.
    // Calculates the next block's difficulty based on the current block's elapsed time
    // and the desired mining time for a block, which is 60 seconds after block 145k.
    //
    // @param _actualTimespan - time elapsed from previous block creation til current block creation;
    // i.e., how much time it took to mine the current block
    // @param _bits - previous block header difficulty (in bits)
    // @return - expected difficulty for the next block
    function calculateDigishieldDifficulty(int64 _actualTimespan, uint32 _bits) external pure returns (uint32 result) {
        int64 retargetTimespan = int64(TARGET_TIMESPAN);
        int64 nModulatedTimespan = int64(_actualTimespan);

        nModulatedTimespan = retargetTimespan + int64(nModulatedTimespan - retargetTimespan) / int64(8); //amplitude filter
        int64 nMinTimespan = retargetTimespan - (int64(retargetTimespan) / int64(4));
        int64 nMaxTimespan = retargetTimespan + (int64(retargetTimespan) / int64(2));

        // Limit adjustment step
        if (nModulatedTimespan < nMinTimespan) {
            nModulatedTimespan = nMinTimespan;
        } else if (nModulatedTimespan > nMaxTimespan) {
            nModulatedTimespan = nMaxTimespan;
        }

        // Retarget
        uint bnNew = targetFromBits(_bits);
        bnNew = bnNew * uint(nModulatedTimespan);
        bnNew = uint(bnNew) / uint(retargetTimespan);

        if (bnNew > POW_LIMIT) {
            bnNew = POW_LIMIT;
        }

        return toCompactBits(bnNew);
    }

    // @dev - shift information to the right by a specified number of bits
    //
    // @param _val - value to be shifted
    // @param _shift - number of bits to shift
    // @return - `_val` shifted `_shift` bits to the right, i.e. divided by 2**`_shift`
    function shiftRight(uint _val, uint _shift) private pure returns (uint) {
        return _val / uint(2)**_shift;
    }

    // @dev - shift information to the left by a specified number of bits
    //
    // @param _val - value to be shifted
    // @param _shift - number of bits to shift
    // @return - `_val` shifted `_shift` bits to the left, i.e. multiplied by 2**`_shift`
    function shiftLeft(uint _val, uint _shift) private pure returns (uint) {
        return _val * uint(2)**_shift;
    }

    // @dev - get the number of bits required to represent a given integer value without losing information
    //
    // @param _val - unsigned integer value
    // @return - given value's bit length
    function bitLen(uint _val) private pure returns (uint length) {
        uint int_type = _val;
        while (int_type > 0) {
            int_type = shiftRight(int_type, 1);
            length += 1;
        }
    }

    // @dev - Convert uint256 to compact encoding
    // based on https://github.com/petertodd/python-bitcoinlib/blob/2a5dda45b557515fb12a0a18e5dd48d2f5cd13c2/bitcoin/core/serialize.py
    // Analogous to arith_uint256::GetCompact from C++ implementation
    //
    // @param _val - difficulty in target format
    // @return - difficulty in bits format
    function toCompactBits(uint _val) private pure returns (uint32) {
        uint nbytes = uint (shiftRight((bitLen(_val) + 7), 3));
        uint32 compact = 0;
        if (nbytes <= 3) {
            compact = uint32 (shiftLeft((_val & 0xFFFFFF), 8 * (3 - nbytes)));
        } else {
            compact = uint32 (shiftRight(_val, 8 * (nbytes - 3)));
            compact = uint32 (compact & 0xFFFFFF);
        }

        // If the sign bit (0x00800000) is set, divide the mantissa by 256 and
        // increase the exponent to get an encoding without it set.
        if ((compact & 0x00800000) > 0) {
            compact = uint32(shiftRight(compact, 8));
            nbytes += 1;
        }

        return compact | uint32(shiftLeft(nbytes, 24));
    }
}
pragma solidity ^0.4.23;


/**
 * @title Eliptic curve signature operations
 *
 * @dev Based on https://gist.github.com/axic/5b33912c6f61ae6fd96d6c4a47afde6d
 *
 * TODO Remove this library once solidity supports passing a signature to ecrecover.
 * See https://github.com/ethereum/solidity/issues/864
 *
 */

library ECRecovery {

  /**
   * @dev Recover signer address from a message by using their signature
   * @param hash bytes32 message, the hash is the signed message. What is recovered is the signer address.
   * @param sig bytes signature, the signature is generated using web3.eth.sign()
   */
  function recover(bytes32 hash, bytes sig)
    internal
    pure
    returns (address)
  {
    bytes32 r;
    bytes32 s;
    uint8 v;

    // Check the signature length
    if (sig.length != 65) {
      return (address(0));
    }

    // Divide the signature in r, s and v variables
    // ecrecover takes the signature parameters, and the only way to get them
    // currently is to use assembly.
    // solium-disable-next-line security/no-inline-assembly
    assembly {
      v := byte(0, mload(add(sig, 32))) // 0
      r := mload(add(sig, 33)) // 1
      s := mload(add(sig, 65)) // 33
    }

    // Version of signature should be 27 or 28, but 0 and 1 are also possible versions
    if (v < 27) {
      v += 27;
    }

    // If the version is correct return the signer address
    if (v != 27 && v != 28) {
      return (address(0));
    } else {
      // solium-disable-next-line arg-overflow
      return ecrecover(hash, v, r, s);
    }
  }

  /**
   * toEthSignedMessageHash
   * @dev prefix a bytes32 value with "\x19Ethereum Signed Message:"
   * @dev and hash the result
   */
  function toEthSignedMessageHash(bytes32 hash)
    internal
    pure
    returns (bytes32)
  {
    // 32 is the length in bytes of hash,
    // enforced by the type signature above
    return keccak256(
      abi.encodePacked("\x19Ethereum Signed Message:\n32",
      hash)
    );
  }
}

pragma solidity ^0.4.8;

contract DogeToken is HumanStandardToken(0, "DogeToken", 8, "WDOGE"), TransactionProcessor {

    using SafeMath for uint;

    // Lock constants
    uint public constant MIN_LOCK_VALUE = 300000000; // 3 doges
    uint public constant OPERATOR_LOCK_FEE = 10; // 1 = 0.1%
    uint public constant SUPERBLOCK_SUBMITTER_LOCK_FEE = 10; // 1 = 0.1%

    // Unlock constants
    uint public constant MIN_UNLOCK_VALUE = 300000000; // 3 doges
    uint public constant OPERATOR_UNLOCK_FEE = 10; // 1 = 0.1%
    uint constant DOGE_TX_BASE_FEE = 50000000; // 0.5 doge
    uint constant DOGE_TX_FEE_PER_INPUT = 100000000; // 1 doge

    // Error codes
    uint constant ERR_OPERATOR_SIGNATURE = 60010;
    uint constant ERR_OPERATOR_ALREADY_CREATED = 60015;
    uint constant ERR_OPERATOR_NOT_CREATED_OR_WRONG_SENDER = 60020;
    uint constant ERR_OPERATOR_HAS_BALANCE = 60030;
    uint constant ERR_OPERATOR_WITHDRAWAL_NOT_ENOUGH_BALANCE = 60040;
    uint constant ERR_OPERATOR_WITHDRAWAL_COLLATERAL_WOULD_BE_TOO_LOW = 60050;
    uint constant ERR_PROCESS_OPERATOR_NOT_CREATED = 60060;
    uint constant ERR_PROCESS_TX_ALREADY_PROCESSED = 60070;
    uint constant ERR_UNLOCK_MIN_UNLOCK_VALUE = 60080;
    uint constant ERR_UNLOCK_USER_BALANCE = 60090;
    uint constant ERR_UNLOCK_OPERATOR_NOT_CREATED = 60100;
    uint constant ERR_UNLOCK_OPERATOR_BALANCE = 60110;    
    uint constant ERR_UNLOCK_NO_AVAILABLE_UTXOS = 60120;
    uint constant ERR_UNLOCK_UTXOS_VALUE_LESS_THAN_VALUE_TO_SEND = 60130;
    uint constant ERR_UNLOCK_VALUE_TO_SEND_LESS_THAN_FEE = 60140;
    uint constant ERR_UNLOCK_BAD_ADDR_LENGTH = 60150;
    uint constant ERR_UNLOCK_BAD_ADDR_PREFIX = 60160;
    uint constant ERR_UNLOCK_BAD_ADDR_CHAR = 60170;
    uint constant ERR_LOCK_MIN_LOCK_VALUE = 60180;

    // Variables set by constructor

    // Contract to trust for tx included in a doge block verification.
    // Only doge txs relayed from trustedRelayerContract will be accepted.
    address public trustedRelayerContract;
    // Doge-Eth price oracle to trust.
    address public trustedDogeEthPriceOracle;
    // Number of times the eth collateral operator should cover her doge holdings 
    uint8 public collateralRatio;


    // counter for next unlock
    uint32 public unlockIdx;
    // Unlocks for which the investor has not sent a proof of unlock yet.
    mapping (uint32 => Unlock) public unlocksPendingInvestorProof;
    // Doge-Eth currencies current market price.
    uint public dogeEthPrice;
    // operatorPublicKeyHash to Operator
    mapping (bytes20 => Operator) public operators;
    OperatorKey[] public operatorKeys;

    // Doge transactions that were already processed by processTransaction()
    Set.Data dogeTxHashesAlreadyProcessed;

    event ErrorDogeToken(uint err);
    event NewToken(address indexed user, uint value);
    event UnlockRequest(uint32 id, bytes20 operatorPublicKeyHash);

    // Represents an unlock request
    struct Unlock {
        address from;
        bytes20 dogeAddress;
        uint value;
        uint operatorFee;
        uint timestamp;
        // Values are indexes in storage array "utxos"
        uint32[] selectedUtxos;
        uint dogeTxFee;
        bytes20 operatorPublicKeyHash;
    }

    struct Utxo {
        uint value;
        uint txHash;
        uint16 index;
    }

    struct Operator {
        address ethAddress;
        uint dogeAvailableBalance;
        uint dogePendingBalance;
        Utxo[] utxos;
        uint32 nextUnspentUtxoIndex;
        uint ethBalance;
        uint24 operatorKeyIndex;
    }

    struct OperatorKey { 
        bytes20 key; 
        bool deleted;
    }

    constructor (address _trustedRelayerContract, address _trustedDogeEthPriceOracle, uint8 _collateralRatio) public {
        trustedRelayerContract = _trustedRelayerContract;
        trustedDogeEthPriceOracle = _trustedDogeEthPriceOracle;
        collateralRatio = _collateralRatio;
    }

    // Adds an operator
    // @param operatorPublicKeyCompressed operator compressed public key (33 bytes). 
    //                          operatorPublicKeyCompressed[0] = odd (0x02 or 0x03)
    //                          operatorPublicKeyCompressed[1-32] = x
    // @param signature doubleSha256(msg.sender) signed by operator (65 bytes).
    //                  signature[0] = v
    //                  signature[1-32] = r
    //                  signature[33-64] = s
    function addOperator(bytes operatorPublicKeyCompressed, bytes signature) public {
        //log0(bytes32(operatorPublicKeyCompressed.length));
        //log0(bytes32(signature.length));

        // Parse operatorPublicKeyCompressed
        bytes32 operatorPublicKeyX;
        bool operatorPublicKeyOdd;
        operatorPublicKeyOdd = operatorPublicKeyCompressed[0] == 0x03;
        assembly {
            operatorPublicKeyX := mload(add(operatorPublicKeyCompressed, 0x21))
        }
        //log1(operatorPublicKeyX, bytes32(operatorPublicKeyOdd ? 1 : 0));

        // Check the non compressed version of operatorPublicKeyCompressed signed msg.sender hash
        bytes32 signedMessage = sha256(abi.encodePacked(sha256(abi.encodePacked(msg.sender))));
        //log1(bytes20(msg.sender), signedMessage);
        address recoveredAddress = ECRecovery.recover(signedMessage, signature);
        //log1(bytes32(recoveredAddress),
        //     bytes32(DogeMessageLibrary.pub2address(uint(operatorPublicKeyX), operatorPublicKeyOdd)));                
        if (recoveredAddress != DogeMessageLibrary.pub2address(uint(operatorPublicKeyX), operatorPublicKeyOdd)) {
            emit ErrorDogeToken(ERR_OPERATOR_SIGNATURE);
            return;
        }
        // Create operator
        bytes20 operatorPublicKeyHash = DogeMessageLibrary.pub2PubKeyHash(operatorPublicKeyX, operatorPublicKeyOdd);
        //log0(operatorPublicKeyHash);
        Operator storage operator = operators[operatorPublicKeyHash];
        // Check that operator does not exist yet
        //log1(bytes20(operator.ethAddress), bytes32((operator.ethAddress == 0) ? 0 : 1));
        if (operator.ethAddress != 0) {
            emit ErrorDogeToken(ERR_OPERATOR_ALREADY_CREATED);
            return;
        }
        operator.ethAddress = msg.sender;
        operator.operatorKeyIndex = uint24(operatorKeys.length);
        operatorKeys.push(OperatorKey(operatorPublicKeyHash, false));
        
    }

    function deleteOperator(bytes20 operatorPublicKeyHash) public {
        Operator storage operator = operators[operatorPublicKeyHash];
        if (operator.ethAddress != msg.sender) {
            emit ErrorDogeToken(ERR_OPERATOR_NOT_CREATED_OR_WRONG_SENDER);
            return;
        }
        if (operator.dogeAvailableBalance != 0 || operator.dogePendingBalance != 0 || operator.ethBalance != 0) {
            emit ErrorDogeToken(ERR_OPERATOR_HAS_BALANCE);
            return;
        }

        OperatorKey storage operatorKey = operatorKeys[operator.operatorKeyIndex]; 
        operatorKey.deleted = true;
        delete operators[operatorPublicKeyHash];
    }

    function getOperatorsLength() public view returns (uint24) {
        return uint24(operatorKeys.length);
    }

    function addOperatorDeposit(bytes20 operatorPublicKeyHash) public payable {
        Operator storage operator = operators[operatorPublicKeyHash];
        if (operator.ethAddress != msg.sender) {
            emit ErrorDogeToken(ERR_OPERATOR_NOT_CREATED_OR_WRONG_SENDER);
            return;
        }
        operator.ethBalance = operator.ethBalance.add(msg.value);
    }

    function withdrawOperatorDeposit(bytes20 operatorPublicKeyHash, uint value) public {
        Operator storage operator = operators[operatorPublicKeyHash];
        if (operator.ethAddress != msg.sender) {
            emit ErrorDogeToken(ERR_OPERATOR_NOT_CREATED_OR_WRONG_SENDER);
            return;
        }
        if (operator.ethBalance < value) {
            emit ErrorDogeToken(ERR_OPERATOR_WITHDRAWAL_NOT_ENOUGH_BALANCE);
            return;
        }
        if ((operator.ethBalance.sub(value)).div(dogeEthPrice) <
            (operator.dogeAvailableBalance.add(operator.dogePendingBalance)).mul(collateralRatio)) {
            emit ErrorDogeToken(ERR_OPERATOR_WITHDRAWAL_COLLATERAL_WOULD_BE_TOO_LOW);
            return;        
        }
        operator.ethBalance = operator.ethBalance.sub(value);
        msg.sender.transfer(value);
    }

    function processTransaction(bytes dogeTx, uint txHash, bytes20 operatorPublicKeyHash, address superblockSubmitterAddress)
        public returns (uint) {
        require(msg.sender == trustedRelayerContract);

        Operator storage operator = operators[operatorPublicKeyHash];
        // Check operator exists 
        if (operator.ethAddress == 0) {
            emit ErrorDogeToken(ERR_PROCESS_OPERATOR_NOT_CREATED);
            return;
        }

        uint value;
        bytes20 firstInputPublicKeyHash;
        address firstInputEthAddress;
        uint16 outputIndex;
        (value, firstInputPublicKeyHash, firstInputEthAddress, outputIndex) = DogeMessageLibrary.parseTransaction(dogeTx, operatorPublicKeyHash);

        // Add tx to the dogeTxHashesAlreadyProcessed
        bool inserted = Set.insert(dogeTxHashesAlreadyProcessed, txHash);
        // Check tx was not already processed
        if (!inserted) {
            emit ErrorDogeToken(ERR_PROCESS_TX_ALREADY_PROCESSED);
            return;        
        }

        // Add utxo
        if (value > 0) {
            operator.utxos.push(Utxo(value, txHash, outputIndex));
        }

        // Update operator's doge balance
        operator.dogeAvailableBalance = operator.dogeAvailableBalance.add(value);

        // See if the first input was signed by the operator
        if (operatorPublicKeyHash != firstInputPublicKeyHash) {
            // this is a lock tx

            if (value < MIN_LOCK_VALUE) {
                emit ErrorDogeToken(ERR_LOCK_MIN_LOCK_VALUE);
                return;
            }

            processLockTransaction(firstInputEthAddress, value,
                                   operator.ethAddress, superblockSubmitterAddress);
            return value;
        } else {
            // this is an unlock tx
            // Update operator's doge balance
            operator.dogePendingBalance = operator.dogePendingBalance.sub(value);
            return 0;
        }
    }

    function wasDogeTxProcessed(uint txHash) public view returns (bool) {
        return Set.contains(dogeTxHashesAlreadyProcessed, txHash);
    }

    function processLockTransaction(address destinationAddress,
                                    uint value, address operatorEthAddress,
                                    address superblockSubmitterAddress) private {
        uint operatorFee = value.mul(OPERATOR_LOCK_FEE) / 1000;
        balances[operatorEthAddress] = balances[operatorEthAddress].add(operatorFee);
        emit NewToken(operatorEthAddress, operatorFee);
        // Hack to make etherscan show the event
        emit Transfer(0, operatorEthAddress, operatorFee);

        uint superblockSubmitterFee = value.mul(SUPERBLOCK_SUBMITTER_LOCK_FEE) / 1000;
        balances[superblockSubmitterAddress] = balances[superblockSubmitterAddress].add(superblockSubmitterFee);
        emit NewToken(superblockSubmitterAddress, superblockSubmitterFee);
        // Hack to make etherscan show the event
        emit Transfer(0, superblockSubmitterAddress, superblockSubmitterFee);

        uint userValue = value.sub(operatorFee).sub(superblockSubmitterFee);
        balances[destinationAddress] = balances[destinationAddress].add(userValue);
        emit NewToken(destinationAddress, userValue);
        // Hack to make etherscan show the event
        emit Transfer(0, destinationAddress, userValue);    
    }


    // Unlock section begin

    // Request ERC20 tokens to be burnt and dogecoins be received on the doge blockchain
    function doUnlock(bytes20 dogeAddress, uint value, bytes20 operatorPublicKeyHash) public returns (bool success) {
        if (value < MIN_UNLOCK_VALUE) {
            emit ErrorDogeToken(ERR_UNLOCK_MIN_UNLOCK_VALUE);
            return;
        }
        if (balances[msg.sender] < value) {
            emit ErrorDogeToken(ERR_UNLOCK_USER_BALANCE);
            return;
        }

        Operator storage operator = operators[operatorPublicKeyHash];
        // Check that operator exists 
        if (operator.ethAddress == 0) {
            emit ErrorDogeToken(ERR_UNLOCK_OPERATOR_NOT_CREATED);
            return;
        }
        // Check that operator available balance is enough
        if (operator.dogeAvailableBalance < value) {
            emit ErrorDogeToken(ERR_UNLOCK_OPERATOR_BALANCE);
            return;
        }

        uint operatorFee = value.mul(OPERATOR_UNLOCK_FEE) / 1000;
        uint unlockValue = value.sub(operatorFee);

        uint32[] memory selectedUtxos;
        uint dogeTxFee;
        uint changeValue;
        uint errorCode;
        (errorCode, selectedUtxos, dogeTxFee, changeValue) = selectUtxosAndFee(unlockValue, operator);
        if (errorCode != 0) {
            emit ErrorDogeToken(errorCode);
            return;
        }

        balances[operator.ethAddress] = balances[operator.ethAddress].add(operatorFee);
        // Hack to make etherscan show the event
        emit Transfer(msg.sender, operator.ethAddress, operatorFee);
        balances[msg.sender] = balances[msg.sender].sub(value);
        // Hack to make etherscan show the event
        emit Transfer(msg.sender, 0, unlockValue);

        emit UnlockRequest(unlockIdx, operatorPublicKeyHash);
        unlocksPendingInvestorProof[unlockIdx] = Unlock(msg.sender, dogeAddress, value, 
                                                        operatorFee,
                                                        block.timestamp, selectedUtxos, dogeTxFee,
                                                        operatorPublicKeyHash);
        // Update operator's doge balance
        operator.dogeAvailableBalance = operator.dogeAvailableBalance.sub(unlockValue.add(changeValue));
        operator.dogePendingBalance = operator.dogePendingBalance.add(changeValue);
        operator.nextUnspentUtxoIndex += uint32(selectedUtxos.length);
        unlockIdx++;
        return true;
    }

    function selectUtxosAndFee(uint valueToSend, Operator operator) private pure returns (uint errorCode, uint32[] memory selectedUtxos, uint dogeTxFee, uint changeValue) {
        // There should be at least 1 utxo available
        if (operator.nextUnspentUtxoIndex >= operator.utxos.length) {
            errorCode = ERR_UNLOCK_NO_AVAILABLE_UTXOS;
            return (errorCode, selectedUtxos, dogeTxFee, changeValue);
        }
        dogeTxFee = DOGE_TX_BASE_FEE;
        uint selectedUtxosValue;
        uint32 firstSelectedUtxo = operator.nextUnspentUtxoIndex;
        uint32 lastSelectedUtxo = firstSelectedUtxo;
        while (selectedUtxosValue < valueToSend && (lastSelectedUtxo < operator.utxos.length)) {
            selectedUtxosValue = selectedUtxosValue.add(operator.utxos[lastSelectedUtxo].value);
            dogeTxFee = dogeTxFee.add(DOGE_TX_FEE_PER_INPUT);
            lastSelectedUtxo++;
        }
        if (selectedUtxosValue < valueToSend) {
            errorCode = ERR_UNLOCK_UTXOS_VALUE_LESS_THAN_VALUE_TO_SEND;
            return (errorCode, selectedUtxos, dogeTxFee, changeValue);
        }
        if (valueToSend <= dogeTxFee) {
            errorCode = ERR_UNLOCK_VALUE_TO_SEND_LESS_THAN_FEE;
            return (errorCode, selectedUtxos, dogeTxFee, changeValue);
        }
        uint32 numberOfSelectedUtxos = lastSelectedUtxo - firstSelectedUtxo;
        selectedUtxos = new uint32[](numberOfSelectedUtxos);
        for(uint32 i = 0; i < numberOfSelectedUtxos; i++) {
            selectedUtxos[i] = i + firstSelectedUtxo;
        }
        changeValue = selectedUtxosValue.sub(valueToSend);
        errorCode = 0;
        return (errorCode, selectedUtxos, dogeTxFee, changeValue);
    }

    function setDogeEthPrice(uint _dogeEthPrice) public {
        require(msg.sender == trustedDogeEthPriceOracle);
        dogeEthPrice = _dogeEthPrice;
    }

    function getUnlockPendingInvestorProof(uint32 index) public view returns (address from, bytes20 dogeAddress, uint value, uint operatorFee, uint timestamp, uint32[] selectedUtxos, uint dogeTxFee, bytes20 operatorPublicKeyHash) {
        Unlock storage unlock = unlocksPendingInvestorProof[index];
        from = unlock.from;
        dogeAddress = unlock.dogeAddress;
        value = unlock.value;
        operatorFee = unlock.operatorFee;
        timestamp = unlock.timestamp;
        selectedUtxos = unlock.selectedUtxos;
        dogeTxFee = unlock.dogeTxFee;
        operatorPublicKeyHash = unlock.operatorPublicKeyHash;
    }

    function getUtxosLength(bytes20 operatorPublicKeyHash) public view returns (uint) {
        Operator storage operator = operators[operatorPublicKeyHash];
        return operator.utxos.length;
    }

    function getUtxo(bytes20 operatorPublicKeyHash, uint i) public view returns (uint value, uint txHash, uint16 index) {
        Operator storage operator = operators[operatorPublicKeyHash];
        Utxo storage utxo = operator.utxos[i];
        return (utxo.value, utxo.txHash, utxo.index);
    }

    // Unlock section end
}