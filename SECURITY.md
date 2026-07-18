# Security Policy

## Reporting a Vulnerability

The JavaParser team takes security issues seriously. We appreciate coordinated
disclosure and will work with you to assess and address valid reports.

**Please do not report security vulnerabilities through public GitHub issues,
discussions, or pull requests.**

Instead, please use GitHub's private vulnerability reporting feature:

1. Go to the [Security tab](https://github.com/javaparser/javaparser/security) of this repository.
2. Click **"Report a vulnerability"**.
3. Fill in the advisory form with as much detail as possible.

This creates a private channel between you and the maintainers. See the
[GitHub documentation on privately reporting a security vulnerability](https://docs.github.com/en/code-security/security-advisories/guidance-on-reporting-and-writing-information-about-vulnerabilities/privately-reporting-a-security-vulnerability)
for more details.

### What to include

To help us triage and fix the issue quickly, please include:

- A description of the vulnerability and its potential impact.
- The affected version(s) of JavaParser.
- Steps to reproduce, ideally with a minimal proof of concept.
- Any suggested fix or mitigation, if you have one.

### What to expect

- We will acknowledge your report and keep you informed of our progress.
- Please allow us a reasonable time to investigate and release a fix before
  any public disclosure.
- We will credit reporters in the security advisory unless you prefer to
  remain anonymous.

## Supported Versions

Security fixes are applied to the latest release. We recommend always using
the most recent version of JavaParser.

## Scope

JavaParser is a library that parses Java source code provided by the
application embedding it. Reports are in scope when they describe a security
impact on the application using the library (for example, denial of service
through resource exhaustion when parsing untrusted input). Bugs without a
security impact should be reported as regular
[GitHub issues](https://github.com/javaparser/javaparser/issues).
