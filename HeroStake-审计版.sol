pragma solidity ^0.6.12;

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
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
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
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
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
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
            bytes32 accountHash
         = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            codehash := extcodehash(account)
        }
        return (codehash != accountHash && codehash != 0x0);
    }
    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );
        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }
    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return functionCall(target, data, "Address: low-level call failed");
    }
    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }
    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
            functionCallWithValue(
                target,
                data,
                value,
                "Address: low-level call with value failed"
            );
    }
    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        return _functionCallWithValue(target, data, value, errorMessage);
    }
    function _functionCallWithValue(
        address target,
        bytes memory data,
        uint256 weiValue,
        string memory errorMessage
    ) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");
        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value: weiValue}(
            data
        );
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly
                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}
/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }
    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }
    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.
        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}
interface IERC20 {
    function totalSupply() external view returns (uint256);
    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);
    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);
    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);
    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);
    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);
    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }
    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}
contract Ownable is Context {
    address private _owner;
    address private _previousOwner;
    uint256 private _lockTime;
    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );
    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }
    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }
    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }
    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }
    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
    function geUnlockTime() public view returns (uint256) {
        return _lockTime;
    }
    //Locks the contract for owner for the amount of time provided
    function lock(uint256 time) public virtual onlyOwner {
        _previousOwner = _owner;
        _owner = address(0);
        _lockTime = now + time;
        emit OwnershipTransferred(_owner, address(0));
    }
    //Unlocks the contract for owner when _lockTime is exceeds
    function unlock() public virtual {
        require(
            _previousOwner == msg.sender,
            "You don't have permission to unlock"
        );
        require(now > _lockTime, "Contract is locked until 7 days");
        emit OwnershipTransferred(_owner, _previousOwner);
        _owner = _previousOwner;
    }
}
// pragma solidity >=0.5.0;
interface IUniswapV2Factory {
    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );
    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);
    function getPair(address tokenA, address tokenB)
        external
        view
        returns (address pair);
    function allPairs(uint256) external view returns (address pair);
    function allPairsLength() external view returns (uint256);
    function createPair(address tokenA, address tokenB)
        external
        returns (address pair);
    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}
// pragma solidity >=0.5.0;
interface IUniswapV2Pair {
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
    event Transfer(address indexed from, address indexed to, uint256 value);
    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint256);
    function balanceOf(address owner) external view returns (uint256);
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);
    function approve(address spender, uint256 value) external returns (bool);
    function transfer(address to, uint256 value) external returns (bool);
    function transferFrom(
        address from,
        address to,
        uint256 value
    ) external returns (bool);
    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint256);
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;
    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(
        address indexed sender,
        uint256 amount0,
        uint256 amount1,
        address indexed to
    );
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);
    function MINIMUM_LIQUIDITY() external pure returns (uint256);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves()
        external
        view
        returns (
            uint112 reserve0,
            uint112 reserve1,
            uint32 blockTimestampLast
        );
    function price0CumulativeLast() external view returns (uint256);
    function price1CumulativeLast() external view returns (uint256);
    function kLast() external view returns (uint256);
    function mint(address to) external returns (uint256 liquidity);
    function burn(address to)
        external
        returns (uint256 amount0, uint256 amount1);
    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external;
    function skim(address to) external;
    function sync() external;
    function initialize(address, address) external;
}
// pragma solidity >=0.6.2;
interface IUniswapV2Router01 {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);
    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    )
        external
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        );
    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (
            uint256 amountToken,
            uint256 amountETH,
            uint256 liquidity
        );
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB);
    function removeLiquidityETH(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountToken, uint256 amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountA, uint256 amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountToken, uint256 amountETH);
    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);
    function swapTokensForExactTokens(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);
    function swapExactETHForTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);
    function swapTokensForExactETH(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);
    function swapExactTokensForETH(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);
    function swapETHForExactTokens(
        uint256 amountOut,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);
    function quote(
        uint256 amountA,
        uint256 reserveA,
        uint256 reserveB
    ) external pure returns (uint256 amountB);
    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountOut);
    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountIn);
    function getAmountsOut(uint256 amountIn, address[] calldata path)
        external
        view
        returns (uint256[] memory amounts);
    function getAmountsIn(uint256 amountOut, address[] calldata path)
        external
        view
        returns (uint256[] memory amounts);
}
// pragma solidity >=0.6.2;
interface IUniswapV2Router02 is IUniswapV2Router01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountETH);
    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}
contract HeroStake is Ownable{
    using SafeMath for uint256;
    using SafeERC20 for IERC20;
    //test net
    // address private constant uniswapRouterAddress = address(0x07d090e7FcBC6AFaA507A3441C7c5eE507C457e6);
    //main net
    address private constant uniswapRouterAddress = address(0x10ED43C718714eb63d5aA57B78B54704E256024E);

    address public profitAddress = address(0xbA55C0a7D2dC9983d9164b69005204C997FAEd64);

    //usdt test address
    // address public usdtAddress = address(0x337610d27c682E347C9cD60BD4b3b107C9d34dDd);
    //usdt main address
    address public usdtAddress = address(0x55d398326f99059fF775485246999027B3197955);
    bool public _isDIS = true;

    IERC20 _Token; 
    struct stakeToken{
        // string name;
        IERC20 tokenAddress;
        bool isExist;
        uint256 minAmount;
        uint256 total;
    }
    mapping(address=>stakeToken) public stakeTokenMap; 

    uint256 public staticProfitRatio = 40;
    uint256 public gameProfitRatio = 5;
    address public gameProfitAddress = address(0x5C3BCEbe95be7B2B5cE7c47aC57601CAdB13E543);

    uint256 public cappingPower = 2000 * 10000 * 10**9;
    
    uint256 public powerToStakeNumber = 100;
    uint256 public maxStakeNumber = 2 * 10**9;

    uint256 public totalOriginalPower = 0;
    uint256 public totalAllPower = 0;

    struct power{
        address userAddress;
        uint256 originalPower;
        uint256 creditPower;
        bool isExist;
        uint256 ljProfit;//
        uint256 receivedProfit;//
        uint256 stakeAverage;//
    }
    mapping(address=>power) powerMap;
    //
    struct destroyLevel{
        uint256 index;//
        uint256 destroyRate;//
        uint256 expandRate;//
    }
    mapping(uint256=>destroyLevel) public destroyLevelMap;
    uint256 public destroyBurnNumber = 0;
    //30% node
    uint256 public _destroyNodeFee = 30;
    //30%
    uint256 public _destroyBurnFee = 30;
    //burn address
    address public burnAddress = address(0x000000000000000000000000000000000000dEaD);
    //40%hero+BNB
    uint256 public _destroyLiquidityFee = 40;
    //Liquidity address
    address public liquidityAddress = address(0xB97043d10120800Fb717fDE7E8fDedC721f32910);

    //hero
    uint256 public liquidityHeroNum = 0;
    //
    uint256 private numAddToLiquidity = 50 * 10**9;//1 yi
    //
    uint256 public redeemRate = 1;
    address public redeemAddress = address(0x0eaBC9e024b381067AF7810fFd4237C36ea55e18);
    //
    uint256 public lastBlockNumber = 0;
    //
    uint256 public stakeTotalStatic = 0;

    //
    uint256 public stakeTotalAverage = 0;

    mapping(address => address) public intros;
    mapping(address => address[]) public children;
    address public constant rootAddress = address(0x61C3cf643201DE464199346B2547C1E94369914f);

    //end

    mapping(address=>mapping(address=>HeroOrder)) _orders;

    mapping(address=>uint256) _takeProfitTime; //
    
    IUniswapV2Router02 public immutable uniswapV2Router;

    uint256 public createBlockNumber = 0;

    uint256 public gasPrice = 2 * 10**5;

    struct HeroOrder{//
        bool isExist;//
        uint256 token;//
        address userAddress;//lp
        address tokenAddress;//lp
        
        uint256 originalPower;//
    }
    //hero
    constructor(
        address tokenAddress
        ) public{
             _Token = IERC20(tokenAddress);
            address[4] memory ads = [
                address(0xd15b556adEaf8001ba41CE87e29aF70Fbd89D029),
                address(0xA9e90Fe8Facff39a76586E47849D6D102C220df1),
                address(0x5B8d0894B347DC387a44A3Dc2615fb729Cd2509f),
                address(0x7ef248c714276616611Bf6271bA53A7D8D96256E)
            ]; 
            for (uint256 index = 0; index < ads.length; index++) {
                setLpToken(ads[index], 0);
            }
            uniswapV2Router = IUniswapV2Router02(uniswapRouterAddress);
        
            destroyLevelMap[1] = destroyLevel(1,0,100);
            destroyLevelMap[2] = destroyLevel(2,10,150);
            destroyLevelMap[3] = destroyLevel(3,20,200);

            createBlockNumber = block.number;
        }
    modifier liquidityAdd(){
        bool overMinTokenBalance = liquidityHeroNum >= numAddToLiquidity;
        if (overMinTokenBalance ) {
            uint256 contractTokenBalance = numAddToLiquidity;
            //add liquidity
            swapAndLiquify(contractTokenBalance);
            liquidityHeroNum = liquidityHeroNum.sub(numAddToLiquidity);
        }
        _;
    }
    function rewardPerToken() public view returns (uint256) {
        if (totalOriginalPower == 0) {
            return stakeTotalAverage;
        }
        (uint256 totalProfit,,) = allPofit();
        //40%,=+/+**40%
        uint256 staticProfit = totalProfit.mul(staticProfitRatio).div(10**2);
        return stakeTotalAverage.add(staticProfit.mul(1e18).div(totalAllPower));
    }
    
    function earned(address account) public view returns (uint256) {
        uint256 totalPower = powerMap[account].originalPower.add(powerMap[account].creditPower);
        return totalPower.mul(rewardPerToken().sub(powerMap[account].stakeAverage)).div(1e18).add(powerMap[account].ljProfit);
    }
    
    function getProfitToken() public view returns(uint256,uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        (uint256 totalProfit,,) = allPofit();
        totalProfit = totalProfit.mul(staticProfitRatio).div(10**2).add(stakeTotalStatic);
        return (earned(msg.sender),totalProfit);
    }
        /**
        HeroToken

payable


0

createOrder
         */
    function heroToken(address lpAddress,uint256 amount,uint256 destroyNo) public liquidityAdd isBindIntro changeAverage(msg.sender){
        require(_isDIS,"is disable");
        require(amount>stakeTokenMap[lpAddress].minAmount,"less token");
        IERC20(lpAddress).safeTransferFrom(address(msg.sender),address(this),amount);
        //lp
        uint256 lpPrice = amount;//lphero
        
        tokenDestroy(destroyNo,lpPrice);
        
        uint256 addPower = lpPrice.mul(destroyLevelMap[destroyNo].expandRate).div(10**2).div(10**6);
        addPower = addPower.mul(10**6);
        if(powerMap[msg.sender].isExist == false){
            powerMap[msg.sender] = power(msg.sender,addPower,0,true,0,0,stakeTotalAverage);
        }else{
            powerMap[msg.sender].originalPower = powerMap[msg.sender].originalPower.add(addPower);
        }
        
        totalOriginalPower = totalOriginalPower.add(addPower);
        totalAllPower = totalAllPower.add(addPower);

        
        createOrder(lpAddress,amount,addPower);
        
        stakeTokenMap[lpAddress].total = stakeTokenMap[lpAddress].total.add(amount);

        emit Pledge(msg.sender, lpAddress, addPower, block.timestamp);
    }
    function createOrder(address lpAddress,uint256 trcAmount, uint256 addPower) private{
         if(_orders[msg.sender][lpAddress].isExist==false){
            _orders[msg.sender][lpAddress]  = HeroOrder(true,trcAmount,msg.sender,lpAddress,addPower);
        }else{
            HeroOrder storage order = _orders[msg.sender][lpAddress];
            order.token = order.token.add(trcAmount);
            order.originalPower = order.originalPower.add(addPower);
        }
        
    }
    function tokenDestroy(uint256 destroyNo,uint256 lpPrice) private{
        if(destroyLevelMap[destroyNo].destroyRate>0){
            uint256 destroyLpNum = lpPrice.mul(destroyLevelMap[destroyNo].destroyRate).div(10**2);//hero
            // address[] memory mPath = new address[](2);
            // mPath[0] =  usdtAddress;
            // mPath[1] =  address(_Token);
            // uint256 heroDestroyPrice = uniswapV2Router.getAmountsOut(destroyLpNum, mPath)[1];//hero
            uint256 heroDestroyPrice = destroyLpNum;
            _Token.safeTransferFrom(address(msg.sender),address(this),heroDestroyPrice);//hero

            //10%20%
            //30%
            uint256 heroDestroyNum = heroDestroyPrice.mul(_destroyBurnFee).div(10**2);
            _Token.safeTransfer(burnAddress,heroDestroyNum);
            //40%
            liquidityHeroNum = liquidityHeroNum.add(heroDestroyPrice.mul(_destroyLiquidityFee).div(10**2));
            uint256 destroyNodeHeroNum = heroDestroyPrice.mul(_destroyNodeFee).div(10**2);
            
            destroyBurnNumber = destroyBurnNumber.add(heroDestroyNum);

            emit DestroyToken(destroyNodeHeroNum, block.timestamp);
        }
    }
    //,NFT5%
    function allPofit() private view returns(uint256,uint256,uint256){
        if(totalOriginalPower>0){
            uint256 onepPofit = totalOriginalPower.mul(powerToStakeNumber).div(10**9);
            if(onepPofit>maxStakeNumber){
                onepPofit = maxStakeNumber;
            }
            
            uint256 number = block.number.sub(lastBlockNumber);
            
            uint256 leftNumber =maxStakeNumber.sub(onepPofit).mul(number);
            
            uint256 totalProfit = onepPofit.mul(number);
            //NFT5%
            uint256 gameProfit = totalProfit.mul(gameProfitRatio).div(10**2);
            return (totalProfit,leftNumber,gameProfit);
        }
        return (0,0,0);
    }
    function getApy()public view returns(uint256){
        if(totalOriginalPower==0){
            return 0;
        }
        uint256 onepPofit = totalOriginalPower.mul(powerToStakeNumber).div(10**9);
        if(onepPofit>maxStakeNumber){
            onepPofit = maxStakeNumber;
        }
        uint256 apy = onepPofit.mul(10**9).mul(28800).mul(365).div(totalOriginalPower);
        return apy;
    }
    /**
    takeProfit

    
ERC20
86400
_precentUp_precentDown100%

ERC20
    */
    function takeProfit() public liquidityAdd changeAverage(msg.sender){
        require(address(msg.sender)==address(tx.origin),"no contract");
        uint256 takeToken = powerMap[msg.sender].ljProfit;
        require(powerMap[msg.sender].ljProfit>0,"not Profit");

        powerMap[msg.sender].ljProfit = 0;
        powerMap[msg.sender].receivedProfit = powerMap[msg.sender].receivedProfit.add(takeToken);
        _Token.safeTransfer(msg.sender,takeToken);
    
        emit ReceiveProfit(msg.sender, takeToken, block.timestamp);
    }
    /**
    takeToken

    */
    function takeToken(uint256 takeRate,address lpAddress)public liquidityAdd changeAverage(msg.sender){
        require(address(msg.sender)==address(tx.origin),"no contract");
        require(_orders[msg.sender][lpAddress].token>0,"less token");

        //token
        HeroOrder storage order = _orders[msg.sender][lpAddress];
        uint256 amount = _orders[msg.sender][lpAddress].token.mul(takeRate).div(10**2);
        stakeTokenMap[lpAddress].total = stakeTokenMap[lpAddress].total.sub(amount);
        uint256 leftPower = _orders[msg.sender][lpAddress].originalPower.mul(takeRate).div(10**2);
        _orders[msg.sender][lpAddress].originalPower = _orders[msg.sender][lpAddress].originalPower.sub(leftPower);
        totalOriginalPower = totalOriginalPower.sub(leftPower);
        totalAllPower = totalAllPower.sub(leftPower);

        if(order.token==amount){
            order.token=0;
            order.isExist = false;
        }else{
            order.token=order.token.sub(amount);
        }

        
        uint256 redeemFee = amount.mul(redeemRate).div(10**2);
        amount = amount.sub(redeemFee);
        IERC20(lpAddress).safeTransfer(redeemAddress, redeemFee);
        IERC20(lpAddress).safeTransfer(msg.sender, amount);
        emit Reedom(msg.sender, lpAddress, leftPower, block.timestamp);
    }
    mapping(uint256=>bool) isSettlement;
    function extraProfit(address userAddress,uint256 amount,uint256 orderNo)public liquidityAdd onlyProfit{
        require(isSettlement[orderNo]==false, "repeat award");
        isSettlement[orderNo] = true;
        _Token.safeTransfer(userAddress,amount);
    }
    
    function getHeroToken(address tokenAddress) public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        HeroOrder memory order = _orders[msg.sender][tokenAddress];
        return order.token;
    }
    
    
    function getReceiveProfitToken() public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return powerMap[msg.sender].receivedProfit;
    }
    
    function getAllPower() public view returns(uint256,uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return (powerMap[msg.sender].originalPower,powerMap[msg.sender].creditPower);
    }   
    
    function getOrderToken(address tokenAddress) public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return _orders[msg.sender][tokenAddress].token;
    }
    
    function getTokenList(address tokenAddress) public view returns(uint256[2] memory){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return [_orders[msg.sender][tokenAddress].token,_orders[msg.sender][tokenAddress].originalPower];
    }
    modifier changeAverage(address account){
        
        if(lastBlockNumber<block.number){
            stakeTotalAverage = rewardPerToken();
            lastBlockNumber = block.number;
            if (account != address(0)) {
                powerMap[account].ljProfit = earned(account);
                powerMap[account].stakeAverage = stakeTotalAverage;
            }
            (uint256 totalProfit,uint256 leftNumber,uint256 gameProfit) = allPofit();
            
            if(leftNumber>0){
                _Token.safeTransfer(burnAddress,leftNumber);
                destroyBurnNumber = destroyBurnNumber.add(leftNumber);
            }
            if(gameProfit>0){
                _Token.safeTransfer(gameProfitAddress,gameProfit);
            }
            
            stakeTotalStatic = stakeTotalStatic.add(totalProfit.mul(staticProfitRatio).div(10**2));
        }
        _;
    }
    
    modifier isBindIntro() {
        require(intros[msg.sender] != address(0) || msg.sender == rootAddress, 'intro no bound');
        _;
    }
    
    function bindIntro (address _intro) external {
       require(intros[msg.sender] == address(0) && msg.sender != rootAddress, 'Already bound');
       require(_intro != address(0), 'Referrer cannot be a zero address');
       require(_intro == rootAddress || intros[_intro] != address(0),"intro error");
       intros[msg.sender] = _intro;
       children[_intro].push(msg.sender);
       emit BindIntroLogs(msg.sender, _intro, block.timestamp);
    }
    
    function isActive (address _user) external view returns(bool) {
      if(intros[_user] != address(0) || _user == rootAddress) {
         return true;
      }
      return false;
    }
    function getTotalHero(address lpAddress) public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return stakeTokenMap[lpAddress].total;
    }
    function changeIsDis(bool flag) public onlyOwner{
        _isDIS = flag;
    }
    function nowTime() public view returns (uint256) {
        return block.timestamp;
    }
    //lptoken
    function setLpToken(address tokenAddress,uint256 _minAmount) public onlyOwner() {
        require(stakeTokenMap[tokenAddress].isExist==false,"lp is exist");
        //lplp
        stakeTokenMap[tokenAddress] =stakeToken(IERC20(tokenAddress),true,_minAmount,0);
        //lp,
        // address uniswapV2Pair = IUniswapV2Factory(uniswapV2Router.factory()).createPair(address(this), uniswapV2Router.WETH());
        // stakeTokenMap[tokenAddress] = stakeToken(IERC20(uniswapV2Pair),true,_minAmount);
    }
    //Hero price
    function getHeroPrice(uint256 amount) public view returns(uint256){
        address[] memory mPath = new address[](2);
        mPath[0] =  address(_Token);
        mPath[1] =  usdtAddress;
        uint256[] memory lpPrices = uniswapV2Router.getAmountsOut(amount, mPath);//lpusdt
        uint256 lpPrice = lpPrices[1];
        return lpPrice;
    }
    //Stake number
    function getStakePlanTotal() public view returns(uint256){
        return block.number.sub(createBlockNumber).mul(maxStakeNumber);
    }

    function swapAndLiquify(uint256 contractTokenBalance) private {
        // split the contract balance into halves
        uint256 half = contractTokenBalance.div(2);
        uint256 otherHalf = contractTokenBalance.sub(half);

        // capture the contract's current ETH balance.
        // this is so that we can capture exactly the amount of ETH that the
        // swap creates, and not make the liquidity event include any ETH that
        // has been manually sent to the contract
        uint256 initialBalance = address(this).balance;

        // swap tokens for ETH
        swapTokensForEth(half); // <- this breaks the ETH -> HATE swap when swap+liquify is triggered

        // how much ETH did we just swap into?
        uint256 receivedEth = address(this).balance.sub(initialBalance);

        // add liquidity to uniswap
        addLiquidity(otherHalf, receivedEth);
        
        emit SwapAndLiquify(half, receivedEth, otherHalf);
    }
    function swapTokensForEth(uint256 tokenAmount) private {
        // generate the uniswap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = address(_Token);
        path[1] = uniswapV2Router.WETH();

        _Token.approve(address(uniswapV2Router), tokenAmount);

        // make the swap
        uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(this),
            block.timestamp
        );
    }

    function addLiquidity(uint256 tokenAmount, uint256 ethAmount) private {
        // approve token transfer to cover all possible scenarios
       _Token.approve(address(uniswapV2Router), tokenAmount);

        // add the liquidity
        (uint256 amountToken,,) = uniswapV2Router.addLiquidityETH{value: ethAmount}(
            address(_Token),
            tokenAmount,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
            address(this),
            block.timestamp
        );
        if(amountToken > 0) {
          payable(liquidityAddress).transfer(address(this).balance);
        }
    }
    function extraGas(uint256 orderId) public payable {
        require(msg.value>=gasPrice, "less token");
        payable(profitAddress).transfer(msg.value);
        emit OrderGas(orderId, msg.value);
    }
    function getDestoryNumber()public view returns(uint256){
        (,uint256 leftNumber,) = allPofit();
        return destroyBurnNumber.add(leftNumber);
    }
    //to recieve ETH from uniswapV2Router when swaping
    receive() external payable {}
    
    modifier onlyProfit(){
        require(msg.sender==profitAddress);
        _;
    }
    event SwapAndLiquify(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 tokensIntoLiqudity
    );
    event BindIntroLogs(address hero_address,address intro_address,uint256 time);
    event Pledge(address hero_address,address cointype,uint256 pledgenum,uint256 time);
    event Reedom(address hero_address,address cointype,uint256  unpledgenum,uint256 time);
    event ReceiveProfit(address hero_address,uint256  staticIncome,uint256 time);
    event DestroyToken(uint256  val,uint256 time);
    event OrderGas(uint256 orderId,uint256 number);
}