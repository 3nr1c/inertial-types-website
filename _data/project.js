module.exports = () => {
	let baseurl;

	if (process.env.CI) {
        baseurl = "/inertial-types-website/";
	} else {
		baseurl = "/";	
    }
	return {
		baseurl: baseurl
	};
};