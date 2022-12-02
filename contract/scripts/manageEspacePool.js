/* eslint-disable prefer-const */
/* eslint-disable no-unused-vars */
/* eslint-disable prettier/prettier */
require('dotenv').config();
const {
  conflux,
  account
} = require('./conflux');
const { address } = require('js-conflux-sdk');
const { ethers } = require("ethers");
const eSpacePoolInfo = require("../artifacts/contracts/eSpace/eSpacePoSPool.sol/ESpacePoSPool.json");
const { loadPrivateKey } = require('../utils');

const provider = new ethers.providers.JsonRpcProvider(process.env.ETH_RPC_URL);
const signer = new ethers.Wallet(loadPrivateKey(), provider);
console.log('eSpace singer address: ', signer.address);

async function main() {
  const eSpacePoolAddress = '0x3cbc6f7d406fe9701573fe6ddf28f4f17b5d46a3';  
  
  const eSpacePool = new ethers.Contract(eSpacePoolAddress, eSpacePoolInfo.abi, signer);

  const lockPeriod = await eSpacePool._poolLockPeriod();
  console.log('lockPeriod: ', lockPeriod);


  const tx = await eSpacePool.setLockPeriod(644400);
  await tx.wait();

  console.log('Finished');
}

main().catch(console.log);