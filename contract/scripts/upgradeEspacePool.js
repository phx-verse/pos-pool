require('dotenv').config();
// const { ethers } = require("ethers");
const hre = require("hardhat");
const { ethers } = hre;

async function main() {

    const proxyAddr = '0x3cbc6F7D406fe9701573FE6DdF28f4F17b5d46A3';

    /* const ESpacePoSPool = await ethers.getContractFactory("ESpacePoSPool");
    const pool = await ESpacePoSPool.deploy();
    await pool.deployed();

    console.log('Impl deployed to:', pool.address);

    const proxy = await ethers.getContractAt("Proxy1967", proxyAddr);
    await proxy.upgradeTo(pool.address); */

    const ePool = await ethers.getContractAt("ESpacePoSPool", proxyAddr);

    let tx = await ePool.lend('0x48d15d4eD5C41782cC711F2Cb7b6606AC40d7275', ethers.utils.parseEther('200000'), {gasLimit: 100000});
    await tx.wait();

    /* let tx = await ePool.setLockPeriod(1123200);
    await tx.wait();
    tx = await ePool.setUnlockPeriod(86400);
    await tx.wait(); */

    console.log('Finished');
}

main().catch(console.log);