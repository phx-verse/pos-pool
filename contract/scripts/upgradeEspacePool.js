require('dotenv').config();
// const { ethers } = require("ethers");
const hre = require("hardhat");
const { ethers } = hre;

async function main() {

    const proxyAddr = '0x3cbc6F7D406fe9701573FE6DdF28f4F17b5d46A3';

    /* const ESpacePoSPool = await ethers.getContractFactory("ESpacePoSPool");
    const pool = await ESpacePoSPool.deploy();
    await pool.deployed();

    console.log('New Impl deployed to:', pool.address);

    const proxy = await ethers.getContractAt("Proxy1967", process.env.ESPACE_POOL_ADDRESS);
    await proxy.upgradeTo(pool.address);

    console.log('Finished');
    */
}

main().catch(console.log);