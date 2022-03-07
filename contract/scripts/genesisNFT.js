/* eslint-disable prettier/prettier */
const { conflux, account } = require('./conflux');
const nftContractMeta = require('../artifacts/contracts/PHXPoSPoolNFT.sol/PHXPoSPoolNFT.json');

const TOKEN_URI = 'https://pospool.phxverse.com/NFT/metas/GenesisNFT.json';

const contract = conflux.Contract({
  abi: nftContractMeta.abi,
  bytecode: nftContractMeta.bytecode,
  // address: "cfxtest:achnjxz9rhvct9gsu87n54yept6zn9znt2mem6nmva",
  address: 'cfx:acaemjexx8xx33n9s9jndmyz2871e90x4jw3zfyphy',
});

async function main() {
  // await deploy();
  // await airdropNFT();
}

async function airdropNFT() {
  const targets = require('./genesisStakers.json');
  for(let i = 0; i < 100; i++) {
    await award(targets[i]);
  }
}

async function deploy() {
  const receipt = await contract.constructor().sendTransaction({
    from: account.address,
  }).executed();
  console.log(receipt);
}

async function award(to) {
  const receipt = await contract.awardItem(to, TOKEN_URI).sendTransaction({
    from: account.address
  }).executed();
  console.log(`award item to: ${to} status: ${receipt.outcomeStatus === 0}`);
}

main().catch(console.log);