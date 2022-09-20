// NOTE: this script currently work with only 16v stable version of node

// TODO: git book for the shield

// TODO: add the addresses in the github

// TODO:
// committing out the exit cause some error which need to debug

// TODO: stderr and stdout to work to log the errors

// shimmer works for it , need to configure the errors and stdout efficiently

// TODO: why setting the value issues , assert failed errors to log properly like c === a * b

// TODO: proper strack tracing on which constraint this issue is coming

// TODO: support of the circomlib circuits

// TODO: in first round we dont need the compiler to switch to circom2, we can do that afterwards in the second phase

// TODO: support of git imported circuits

// TODO: ptau estimation from the constraints

// Boiler plate for the whole dapp

// TODO: proper lexical analysis

// more testing/ unit testing to do

// input base path testing for the cicuits

// test case for the empty shield config file

// write about why shield compiler feature is all you need

// compile feature unit testing ( issue , jest could not handle long waiting modes )

// look into husky install

// prepare plan so multiple versions not being released at once

// .sh file cp while building

// issue of already existing the shield cli

// get familier with circom like no one is

// more into circom development

// does our package shows error of circom??

// check the circom syntex before compiling

// giving user the option to check the circuits besides the compiling

// info feature or info flag while compiling

// update the notion of the shield

/*

Fixturess:

witness.json is not generating for invalid input file need to debug this

*/


const DEFAULT_NODE_ARGS = "--max-old-space-size=8192 --stack-size=65500";
const NODE_ARGS = process.env.NODE_ARGS || DEFAULT_NODE_ARGS;
const NODE_CMD = `node ${NODE_ARGS}`;

const { CircomRunner, bindings } = require("circom2");
const { ufs } = require("@phated/unionfs");
const nodefs = require("fs");
const fs = require("fs/promises");
const { Volume, createFsFromVolume } = require("memfs");
const builder = require("./witness");
const { setTimeout } = require("timers");
const shimmer = require("shimmer");
const binFileUtils = require("@iden3/binfileutils");
// const { readR1csHeader, readR1cs } = require("r1csfile");
const readR1cs = require("r1csfile").load;
const readR1csHeader = require("r1csfile").loadHeader;
const { Scalar, utils, ZqField } = require("ffjavascript");
const path = require("path");
const { wtns } = require("snarkjs");
const shelljs = require("shelljs");

const groupOrderPrimeStr =
  "21888242871839275222246405745257275088548364400416034343698204186575808495617";
const groupOrderPrime = BigInt(groupOrderPrimeStr);

async function checkConstraints(F, constraints, witness, signals) {
  console.log({ constraints, witness, signals });
  if (!constraints) {
    throw new Error("empty constraints");
  }
  for (let i = 0; i < constraints.length; i++) {
    console.log("checking single", constraints[i]);
    checkConstraint(constraints[i]);
  }

  function checkConstraint(constraint) {
    console.log(constraint[0]);
    const a = evalLC(constraint[0]);
    const b = evalLC(constraint[1]);
    const c = evalLC(constraint[2]);

    console.log(!F.isZero(F.sub(F.mul(a, b), c)));

    console.log(
      `${displayLc(constraint[0])} * ${displayLc(constraint[1])} != ${displayLc(
        constraint[2]
      )}`
    );

    if (!F.isZero(F.sub(F.mul(a, b), c))) {
      console.log("\nInvalid constraint:");
      console.log(
        `${displayLc(constraint[0])} * ${displayLc(
          constraint[1]
        )} != ${displayLc(constraint[2])}`
      );
      console.log("Related signals:");
      let sigs = new Set();
      for (const c of constraint) {
        for (const s in c) {
          sigs.add(Number(s));
        }
      }
      for (const s of sigs) {
        // signal 0 is 'one'
        if (s != 0) {
          console.log(
            `signal${s}: ${signals[s].join(" ")}, value: ${witness[s]}`
          );
        }
      }
      console.log("please check your circuit and input\n");

      throw new Error("Constraint doesn't match");
    }
  }

  function evalLC(lc) {
    let v = F.zero;
    for (let w in lc) {
      console.log(lc[w]);
      v = F.add(v, F.mul(BigInt(lc[w]), BigInt(witness[w])));
    }
    return v;
  }

  function displayLc(lc) {
    const entries = Object.entries(lc);
    if (entries.length == 0) {
      return "0";
    }
    function displayField(x) {
      const f = BigInt(x);
      // display some field element as negative int for better reading
      if (f >= groupOrderPrime - 200n) {
        return `(-${(groupOrderPrime - f).toString()})`;
      }
      return f.toString();
    }
    function displayMonomial(coef, signalIdx) {
      return `${displayField(coef)}*signal${signalIdx}`;
    }
    return (
      "(" + entries.map((kv) => displayMonomial(kv[1], kv[0])).join(" + ") + ")"
    );
  }
}

async function assertOut(symbols, actualOut, expectedOut) {
  if (!symbols) {
    throw new Error("empty symbols");
  }

  checkObject("main", expectedOut);

  function checkObject(prefix, eOut) {
    if (Array.isArray(eOut)) {
      for (let i = 0; i < eOut.length; i++) {
        checkObject(prefix + "[" + i + "]", eOut[i]);
      }
    } else if (typeof eOut == "object" && eOut.constructor.name == "Object") {
      for (let k in eOut) {
        checkObject(prefix + "." + k, eOut[k]);
      }
    } else {
      if (typeof symbols[prefix] == "undefined") {
        assert(false, "Output variable not defined: " + prefix);
      }
      const ba = actualOut[symbols[prefix].varIdx].toString();
      const be = eOut.toString();
      assert.strictEqual(ba, be, prefix);
    }
  }
}

class Checker {
  r1csFilepath;
  symFilepath;
  r1cs;
  symbols;
  signals;
  constructor(r1csFilepath, symFilepath) {
    this.r1csFilepath = r1csFilepath;
    this.symFilepath = symFilepath;
  }
  async load() {
    console.log("hello world", this.r1csFilepath, true, false);
    this.r1cs = await readR1cs(this.r1csFilepath, true, false);
    console.log("r1cssssssss", this.r1cs.constraints);
    const { symbols, signals } = await readSymbols(this.symFilepath);
    this.symbols = symbols;
    this.signals = signals;
  }

  async checkConstraintsAndOutput(witnessFilePath, expectedOutputFile) {
    // 0. load r1cs and witness
    if (!this.r1cs) {
      await this.load();
    }
    let witness;
    if (witnessFilePath.endsWith("json")) {
      witness = JSON.parse(nodefs.readFileSync(witnessFilePath).toString());
    } else {
      witness = await readWtns(witnessFilePath);
    }
    // 1. check constraints
    const F = new ZqField(this.r1cs.prime);
    const constraints = this.r1cs.constraints;
    console.log({ constraints });
    await checkConstraints(F, constraints, witness, this.signals);
    // 2. check output
    if (expectedOutputFile) {
      if (nodefs.existsSync(expectedOutputFile)) {
        const expectedOutputJson = JSON.parse(
          nodefs.readFileSync(expectedOutputFile).toString()
        );
        await assertOut(this.symbols, witness, expectedOutputJson);
      } else {
        console.log("no output file, skip:", expectedOutputFile);
      }
    }
    return true;
  }
}

const initFS = async () => {
  const vol = Volume.fromJSON({
    "/dev/stdin": "",
    "/dev/stdout": "",
    "/dev/stderr": "",
  });

  const memfs = createFsFromVolume(vol);

  // // Using this order to prefer writing virtual files from the circom2 wasm
  ufs
    .use(nodefs)
    // I hate typescript
    .use(memfs);

  let bufferSize = 10 * 1024 * 1024;
  let writeBuffer = new Uint8Array(bufferSize);
  let writeBufferFd = -1;
  let writeBufferOffset = 0;
  let writeBufferPos = 0;

  console.log();

  const updatesWasmFs = {
    // ...wasmFs.fs,
    ...ufs,
    writeSync(fd, buf, offset, len, pos) {
      if (
        writeBufferFd === fd &&
        writeBufferOffset + len < bufferSize &&
        pos === writeBufferPos + writeBufferOffset
      ) {
        writeBuffer.set(buf, writeBufferOffset);
        writeBufferOffset += len;
        return len;
      } else {
        if (writeBufferFd >= 0) {
          ufs.writeSync(
            writeBufferFd,
            writeBuffer,
            0,
            writeBufferOffset,
            writeBufferPos
          );
        }
        writeBufferFd = fd;
        writeBufferOffset = 0;

        writeBuffer.set(buf, writeBufferOffset);
        writeBufferOffset += len;
        writeBufferPos = pos;
      }
      return len;
    },
    closeSync(fd) {
      if (writeBufferFd >= 0) {
        // console.log("flush")
        ufs.writeSync(
          writeBufferFd,
          writeBuffer,
          0,
          writeBufferOffset,
          writeBufferPos
        );
        writeBufferFd = -1;
        writeBufferOffset = 0;
        writeBufferPos = 0;
      }
      if (fd >= 0) {
        return ufs.closeSync(fd);
      }
    },
    getStdOut() {
      let promise = new Promise((resolve) => {
        resolve(ufs.readFileSync("/dev/stdout", "utf8"));
      });
      return promise;
    },
  };

  updatesWasmFs.writeFileSync("/dev/stderr", "");
  updatesWasmFs.writeFileSync("/dev/stdout", "");

  let stdout = "";
  let stderr = "";
  // We wrap the writeSync function because circom2 doesn't allow us to
  // configure the logging and it doesn't exit with proper exit codes
  shimmer.wrap(updatesWasmFs, "writeSync", function (original) {
    return function (fd, data, offsetOrPosition, lengthOrEncoding, position) {
      // If writing to stdout, we hijack to hide unless debug
      console.log("inside the shimmer function ==========>", {
        fd,
        data: new TextDecoder().decode(data),
        offsetOrPosition,
        lengthOrEncoding,
        position,
      });
      if (fd === 1) {
        if (typeof data === "string") {
          stdout += data;
          // This is a little fragile, but we assume the wasmer-js
          // terminal character is a newline by itself
          console.log("stdout with fd=1 ========>", { stdout });
          if (stdout.endsWith("\n")) {
            const msg = stdout.trim();
            stdout = "";
            console.log("stdout ==========>", { msg });
            // logger.info(msg);
          }
          return data.length;
        } else {
          stdout += new TextDecoder().decode(data);

          console.log("if the data is not type of string", { stdout });
          // This is a little fragile, but we assume the wasmer-js
          // terminal character is a newline by itself
          if (stdout.endsWith("\n")) {
            const msg = stdout.trim();
            stdout = "";
            console.log("stdout ==========>", { msg });
            // logger.info(msg);
          }
          return data.byteLength;
        }
      }

      // If writing to stderr, we hijack and throw an error
      if (fd == 2) {
        if (typeof data === "string") {
          stderr += data;
          // This is a little fragile, but we assume that circom2
          // ends the failed compile with "previous errors were found"
          if (stderr.includes("previous errors were found")) {
            const msg = stderr.trim();
            stderr = "";
            console.log("stdout ==========>", { msg });
            // logger.error(msg);
            throw new Error(msg);
          }
          return data.length;
        } else {
          stderr += new TextDecoder().decode(data);
          // This is a little fragile, but we assume that circom2
          // ends the failed compile with "previous errors were found"
          if (stderr.includes("previous errors were found")) {
            const msg = stderr.trim();
            stderr = "";
            console.log("stdout ==========>", { msg });
            // logger.error(msg);
            throw new Error(msg);
          }
          return data.byteLength;
        }
      }

      if (typeof data === "string") {
        if (typeof lengthOrEncoding !== "number") {
          return original(fd, data, offsetOrPosition, lengthOrEncoding);
        } else {
          throw Error("Invalid arguments");
        }
      } else {
        if (typeof lengthOrEncoding !== "string") {
          return original(
            fd,
            data,
            offsetOrPosition,
            lengthOrEncoding,
            position
          );
        } else {
          throw Error("Invalid arguments");
        }
      }
    };
  });

  return updatesWasmFs;
};

const main = async () => {
  const wasmFs = await initFS();


  const circom = new CircomRunner({
    args: [
      circomPath,
      "--r1cs",
      "--wat",
      "--wasm",
      "--sym",
      "-o",
      "/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/build",
    ],
    env: {},
    // Preopen from the root because we use absolute paths
    preopens: {
      "/": "/",
    },
    bindings: {
      ...bindings,
      fs: wasmFs,
    },
    returnOnExit: true,
  });

  const wasmPath = require.resolve("circom2/circom.wasm");

  const circomWasm = await fs.readFile(wasmPath);

  let instance;
  try {
    instance = await circom.execute(circomWasm);
  } catch (err) {
    console.log({ err });
  }

  console.log({ instance });

  // circom.bindings.fs.closeSync(-1)

  const stderr = wasmFs.readFileSync("/dev/stderr", "utf8");

  console.log({ stderr });

  let stdout = await wasmFs.getStdOut();

  console.log({ stdout });

  const wasmFilePath = `/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/build/Multiplier_js/Multiplier.wasm`;

  const wasmData = ufs.readFileSync(wasmFilePath);

  let logs;

  const witness = await builder(wasmData, {
    log(message, label) {
      if (label) {
        console.log("labellllllssss =============>", { label, message });
        logs.push(label + ": " + message.toString());
      } else {
        console.log("labellllllssss =============>", { label, message });
        logs.push(message.toString());
      }
    },
  });

  console.log("alll logsss ==================>", logs);

  const r1csFilePath = `/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/build/Multiplier.r1cs`;
  const symFilePath = `/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/build/Multiplier.sym`;

  const r1cs = await getR1cs(wasmFs, r1csFilePath);

  console.log({ r1cs });

  const wtnsFile = await witness.calculateWTNSBin(
    {
      a: 2,
      b: 2,
    },
    true
  );

  console.log("witnessss here ============>", { witness });

  console.log("alll logsss ==================>", logs);

  const response = await logOutputs(r1cs, wtnsFile, wasmFs, wasmData);

  console.log("got the response and =====> checking =========>", response);

  const checker = new Checker(r1csFilePath, symFilePath);

  console.log({ checker });

  const witnessFile =
    "/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/debug/witness.json";

  const expectedOutputFile =
    "/home/sleepyqadir/zero-knowledge/snarkit/testdata/num2bits_err/data/err_case01/output.json";

  await checker.checkConstraintsAndOutput(witnessFile, expectedOutputFile);

  console.log("generating files for the solidity using snarks");

  // await generateSnarkJsFiles();
};

const getR1cs = async (wasmFs, r1csFilePath) => {
  let r1cs;
  r1csFile = wasmFs.readFileSync(r1csFilePath);

  console.log({ r1csFile });

  const { fd: fdR1cs, sections: sectionsR1cs } = await binFileUtils.readBinFile(
    r1csFile,
    "r1cs",
    1,
    1 << 22,
    1 << 24
  );
  r1cs = await readR1csHeader(fdR1cs, sectionsR1cs, /* singleThread */ true);
  await fdR1cs.close();
  return r1cs;
};

const logOutputs = async (r1cs, wtnsFile, wasmFs) => {
  if (r1cs && r1cs.nOutputs > 0) {
    const { fd: fdWtns, sections: sectionsWtns } =
      await binFileUtils.readBinFile(wtnsFile, "wtns", 2, 1 << 25, 1 << 23);

    const wtns = await readWtnsHeader(fdWtns, sectionsWtns);
    const buffWitness = await binFileUtils.readSection(fdWtns, sectionsWtns, 2);

    console.log({ wtns, buffWitness });

    let outputPrefixes = {};
    let inputPrefixes = {};
    const symFile = wasmFs.readFileSync(
      `/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/build/Multiplier.sym`
    );
    let lastPos = 0;
    let dec = new TextDecoder("utf-8");
    console.log("length of symFile ===========>", symFile.length);
    for (let i = 0; i < symFile.length; i++) {
      console.log("keysss ===========>", symFile[i]);
      if (symFile[i] === 0x0a) {
        console.log("line ===========>", dec.decode(symFile.slice(lastPos, i)));
        let line = dec.decode(symFile.slice(lastPos, i));
        let wireNo = +line.split(",")[0];
        console.log({ wireNo, ouput: r1cs.nOutputs });
        if (wireNo <= r1cs.nOutputs) {
          outputPrefixes[wireNo] =
            line.split(",")[3].replace("main.", "") + " = ";
        } else {
          inputPrefixes[wireNo] =
            line.split(",")[3].replace("main.", "") + " = ";
        }
        lastPos = i;
      }
    }

    console.log({ outputPrefixes, inputPrefixes });

    let outputSignals = [];
    for (const wire in outputPrefixes) {
      const b = buffWitness.slice(wire * wtns.n8, wire * wtns.n8 + wtns.n8);
      const outputPrefix = outputPrefixes[wire] || "";
      outputSignals.push(outputPrefix + Scalar.fromRprLE(b).toString());
      console.log({ wire }, outputPrefix + Scalar.fromRprLE(b).toString());
    }

    let inputSignals = [];

    for (const wire in inputPrefixes) {
      const b = buffWitness.slice(wire * wtns.n8, wire * wtns.n8 + wtns.n8);
      const outputPrefix = inputPrefixes[wire] || "";
      inputSignals.push(outputPrefix + Scalar.fromRprLE(b).toString());
      console.log({ wire }, outputPrefix + Scalar.fromRprLE(b).toString());
    }

    console.log("ouputtt ============>", outputSignals);
    console.log("input ============>", inputSignals);

    await fdWtns.close();

    console.log(
      "=========================== starkkit =========================================="
    );
    console.log(
      "=========================== starkkit =========================================="
    );
    console.log(
      "=========================== starkkit =========================================="
    );
    console.log(
      "=========================== starkkit =========================================="
    );
    console.log(
      "=========================== starkkit =========================================="
    );

    const wtnsFilePath =
      "/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/debug/witness.json";
    const inputFilePath =
      "/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/debug/input.json";

    await generateWitness(inputFilePath, wtnsFilePath, wasmFs);
  }
};

const readWtnsHeader = async (fd, sections) => {
  await binFileUtils.startReadUniqueSection(fd, sections, 1);
  const n8 = await fd.readULE32();
  const q = await binFileUtils.readBigInt(fd, n8);
  const nWitness = await fd.readULE32();
  await binFileUtils.endReadSection(fd);
  return { n8, q, nWitness };
};

main();

const generateWitness = async (inputFilePath, witnessFilePath, wasmFs) => {
  const snarkjsPath = path.join(require.resolve("snarkjs"), "..", "cli.cjs");
  console.log({ snarkjsPath });
  let witnessBinFile;
  if (witnessFilePath.endsWith(".json")) {
    witnessBinFile = witnessFilePath.replace(/json$/, "wtns");
  } else {
    witnessBinFile = witnessFilePath;
  }
  try {
    var cmd;
    if (
      !witnessFilePath.endsWith(".json") &&
      !witnessFilePath.endsWith(".wtns")
    ) {
      throw new Error("invalid witness file type");
    }

    console.log("input file path", inputFilePath);

    const inputFileData = await wasmFs.readFileSync(inputFilePath, "utf8");

    console.log({ inputFileData });

    const input = utils.unstringifyBigInts(JSON.parse(inputFileData));

    console.log("input file path ==============>", path);

    const binary = `/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/build/Multiplier_js/Multiplier.wasm`;

    console.log({
      input,
      binary,
      witnessBinFile,
      default: defaultWitnessOption(),
    });

    await wtns.calculate(input, binary, witnessBinFile, defaultWitnessOption());

    console.log("witness is calculated ===========>");
  } catch (err) {
    console.log("error in generate witness", err);
  }

  if (witnessFilePath.endsWith(".json")) {
    cmd = `${NODE_CMD} ${snarkjsPath} wej ${witnessBinFile} ${witnessFilePath}`;
    shelljs.exec(cmd);
  }
};

// sanity check is not supported for wasm backend now
// await compileWasmBinary({ circuitDirName, r1csFilepath, circuitFilePath, symFilepath, binaryFilePath, verbose });

function defaultWitnessOption() {
  let logFn = console.log;
  let calculateWitnessOptions = {
    sanityCheck: true,
    logTrigger: logFn,
    logOutput: logFn,
    logStartComponent: logFn,
    logFinishComponent: logFn,
    logSetSignal: logFn,
    logGetSignal: logFn,
  };
  return calculateWitnessOptions;
}

async function readSymbols(path) {
  let symbols = {};
  let signals = {};

  const symsStr = await fs.readFile(path, "utf8");
  const lines = symsStr.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const arr = lines[i].split(",");
    if (arr.length != 4) continue;
    const symbol = arr[3];
    const labelIdx = Number(arr[0]);
    const varIdx = Number(arr[1]);
    const componentIdx = Number(arr[2]);
    symbols[symbol] = {
      labelIdx,
      varIdx,
      componentIdx,
    };
    if (signals[varIdx] == null) {
      signals[varIdx] = [symbol];
    } else {
      signals[varIdx].push(symbol);
    }
  }
  return { symbols, signals };
}

const generateSnarkJsFiles = () => {
  /*
  
  Step1: download the ptau file / TODO: switch this to estimation instead of taking from config

  step2: setup the protocol zkey

  step3: contribution in the protocol

  step4: create verification file

  */

  const INPUT_BASE_PATH =
    "/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/build/";

  const PTAU = "powersOfTau28_hez_final_10.ptau";

  const CIRCUIT_NAME = "Multiplier";

  const ptauCmd = `wget -O "${INPUT_BASE_PATH}${PTAU}" https://hermez.s3-eu-west-1.amazonaws.com/${PTAU}`;

  shelljs.exec(ptauCmd);
  
  const setupCmd = `snarkjs groth16 setup "${INPUT_BASE_PATH}${CIRCUIT_NAME}.r1cs" "${INPUT_BASE_PATH}${PTAU}" "${INPUT_BASE_PATH}circuit_0000.zkey"`;

  shelljs.exec(setupCmd);

  
  const CONTRIBUTER = "This is the test contributer name";

  const ENTROPY = "This is the test entropy";

  const ZKEY = "Multiplier.zkey";

  const contributeCmd = `snarkjs zkey contribute "${INPUT_BASE_PATH}circuit_0000.zkey" "${INPUT_BASE_PATH}${ZKEY}" --name="${CONTRIBUTER}" -v -e="${ENTROPY}"`;

  shelljs.exec(contributeCmd);

  const verficationCmd = `snarkjs zkey export verificationkey "${INPUT_BASE_PATH}${ZKEY}" "${INPUT_BASE_PATH}verification_key.json"`;

  shelljs.exec(verficationCmd);

  const generateSolidityCmd = `snarkjs zkey export solidityverifier "${INPUT_BASE_PATH}${ZKEY}" "/home/sleepyqadir/zero-knowledge/test-circom2/multiplier/contracts/${CIRCUIT_NAME}_Verifier.sol"`;
  shelljs.exec(generateSolidityCmd);
};
