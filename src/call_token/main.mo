import Result "mo:base/Result";
import Principal "mo:base/Principal";
import ExtCore "../ext_token_backend/ext/Core";
// import EXT_TOKEN "../ext_token_backend/main";

actor Call_Token {
    private var TOKEN_CANISTER_ID : Text = "4hw4x-jyaaa-aaaah-aa6qa-cai";
    type Balance = ExtCore.Balance;
    type CommonError = ExtCore.CommonError;

    // let EXT_TOKEN = actor ("q4eej-kyaaa-aaaaa-aaaha-cai") : actor {
    //     EXT_TOKEN : (Text) -> async Text;
    // };

    public func setCanister(canId : Text) : async Bool {
        TOKEN_CANISTER_ID := canId;
        return true;
    };

    public func getCanister() : async Text {
        return TOKEN_CANISTER_ID;
    };

    // public func callSupply() : async Result.Result<Balance, CommonError> {
    //     await EXT_TOKEN.supply();
    // };

    public func callSupply2() : async Result.Result<Balance, CommonError> {
        let cowsay = actor ("q4eej-kyaaa-aaaaa-aaaha-cai") : actor {
            supply : () -> async Result.Result<Balance, CommonError>;
        };
        return await cowsay.supply();
    };
};
