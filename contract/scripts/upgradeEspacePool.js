require('dotenv').config();
// const { ethers } = require("ethers");
const hre = require("hardhat");
const { ethers } = hre;

async function main() {

    const ESpacePoSPool = await ethers.getContractFactory("ESpacePoSPool");
    const pool = await ESpacePoSPool.deploy();
    await pool.deployed();

    console.log('Impl deployed to:', pool.address);

    const proxyAddr = '0x3cbc6F7D406fe9701573FE6DdF28f4F17b5d46A3';

    const proxy = await ethers.getContractAt("Proxy1967", proxyAddr);
    await proxy.upgradeTo(pool.address);

    const ePool = await ethers.getContractAt("ESpacePoSPool", proxyAddr);

    let tx = await ePool.setLockPeriod(2250000);
    await tx.wait();

    tx = await ePool.setUnlockPeriod(176400);
    await tx.wait();

    console.log('Finished');

}

main().catch(console.log);