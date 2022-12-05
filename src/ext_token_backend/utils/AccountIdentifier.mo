/**
Generates AccountIdentifier's for the IC (32 bytes). Use with 
hex library to generate corresponding hex address.
Uses custom SHA224 and CRC32 motoko libraries
 */

import Array "mo:base/Array";
import Blob "mo:base/Blob";
import Buffer "mo:base/Buffer";
import CRC32 "./CRC32";
import Debug "mo:base/Debug";
import Hex "./Hex";
import Nat "mo:base/Nat";
import Nat8 "mo:base/Nat8";
import Option "mo:base/Option";
import Principal "mo:base/Principal";
// import SHA224 "mo:sha224/SHA224";
import SHA224 "./SHA224";
import Text "mo:base/Text";

module {
  public type AccountIdentifier = Text;
  public type SubAccount = [Nat8];

  private let ads : [Nat8] = [10, 97, 99, 99, 111, 117, 110, 116, 45, 105, 100]; //b"\x0Aaccount-id"
  public let SUBACCOUNT_ZERO : [Nat8] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

  //Public functions
  public func fromText(t : Text, sa : ?SubAccount) : AccountIdentifier {
    return fromPrincipal(Principal.fromText(t), sa);
  };
  public func fromPrincipal(p : Principal, sa : ?SubAccount) : AccountIdentifier {
    return fromBlob(Principal.toBlob(p), sa);
  };
  public func fromBlob(b : Blob, sa : ?SubAccount) : AccountIdentifier {
    return fromBytes(Blob.toArray(b), sa);
  };
  public func fromBytes(data : [Nat8], sa : ?SubAccount) : AccountIdentifier {
    var _sa : [Nat8] = SUBACCOUNT_ZERO;
    if (Option.isSome(sa)) {
      _sa := Option.unwrap(sa);
    };
    var hash : [Nat8] = SHA224.sha224(Array.append(Array.append(ads, data), _sa));
    var crc : [Nat8] = CRC32.crc32(hash);
    return Hex.encode(Array.append(crc, hash));
  };

  public let equal = Text.equal;
  public let hash = Text.hash;
};
